# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team
# SPDX-FileCopyrightText: 2012 Plataformatec

defmodule Mix.Tasks.Compile do
  use Mix.Task

  @shortdoc "Compiles source files"

  @moduledoc """
  The main entry point to compile source files.

  It simply runs the compilers registered in your project and returns
  a tuple with the compilation status and a list of diagnostics.

  Before compiling code, it performs a series of checks to ensure all
  dependencies are compiled and the project is up to date. Then the
  code path of your Elixir system is pruned to only contain the dependencies
  and applications that you have explicitly listed in your `mix.exs`.

  ## Configuration

    * `:compilers` - compilers to run, defaults to `Mix.compilers/0`,
      which are `[:erlang, :elixir, :app]`.

    * `:consolidate_protocols` - when `true`, runs protocol
      consolidation after compiling Elixir. The default value is `true`.

    * `:build_path` - the directory where build artifacts
      should be written to. This option is intended only for
      child apps within a larger umbrella application so that
      each child app can use the common `_build` directory of
      the parent umbrella. In a non-umbrella context, configuring
      this has undesirable side-effects (such as skipping some
      compiler checks) and should be avoided.

    * `:prune_code_paths` - prune code paths before compilation. When true
      (default), this prunes code paths of applications that are not listed
      in the project file with dependencies.  When false, this keeps the
      entirety of Erlang/OTP available when the project starts, including
      the paths set by the code loader from the `ERL_LIBS` environment as
      well as explicitly listed by providing `-pa` and `-pz` options
      to Erlang.

  ## Compilers

  To see documentation for each specific compiler, you must
  invoke `help` directly for the compiler command:

      $ mix help compile.elixir
      $ mix help compile.erlang

  You can get a list of all compilers by running:

      $ mix compile --list

  ## Command line options

    * `--all-warnings` (`--no-all-warnings`) - prints all warnings, including previous compilations
      (default is true except on errors)
    * `--erl-config` - path to an Erlang term file that will be loaded as Mix config
    * `--force` - forces compilation
    * `--list` - lists all enabled compilers
    * `--listeners` - starts Mix listeners (they are started by default,
      unless `--no-listeners` or `--no-deps-check` are given)
    * `--no-app-loading` - does not load .app resource file after compilation
    * `--no-archives-check` - skips checking of archives
    * `--no-compile` - does not actually compile, only loads code and perform checks
    * `--no-deps-check` - skips checking of dependencies
    * `--no-elixir-version-check` - does not check Elixir version
    * `--no-listeners` - does not start Mix listeners
    * `--no-optional-deps` - does not compile or load optional deps. Useful for testing
      if a library still successfully compiles without optional dependencies (which is the
      default case with dependencies)
    * `--no-prune-code-paths` - do not prune code paths before compilation, this keeps
      the entirety of Erlang/OTP available when the project starts
    * `--no-protocol-consolidation` - skips protocol consolidation
    * `--no-validate-compile-env` - does not validate the application compile environment
    * `--return-errors` - returns error status and diagnostics instead of exiting on error
    * `--warnings-as-errors` - exit with non-zero status if compilation has one or more
      warnings. Only concerns compilation warnings from the project, not its dependencies.

  """

  @deprecated "Use Mix.Task.Compiler.compilers/1 instead"
  defdelegate compilers(config \\ Mix.Project.config()), to: Mix.Task.Compiler

  @impl true
  def run(["--list"]) do
    # Loadpaths without checks because compilers may be defined in deps.
    args = [
      "--no-elixir-version-check",
      "--no-deps-check",
      "--no-archives-check",
      "--no-listeners"
    ]

    Mix.Task.run("loadpaths", args)
    Mix.Task.reenable("loadpaths")
    Mix.Task.reenable("deps.loadpaths")

    # Compilers are tasks, so load all tasks available.
    _ = Mix.Task.load_all()

    shell = Mix.shell()
    modules = Mix.Task.all_modules()

    docs =
      for module <- modules,
          task = Mix.Task.task_name(module),
          match?("compile." <> _, task),
          doc = Mix.Task.moduledoc(module) do
        {task, first_line(doc)}
      end

    max =
      Enum.reduce(docs, 0, fn {task, _}, acc ->
        max(byte_size(task), acc)
      end)

    sorted = Enum.sort(docs)

    Enum.each(sorted, fn {task, doc} ->
      shell.info(format(~c"mix ~-#{max}s # ~ts", [task, doc]))
    end)

    consolidate_protocols? = Mix.Project.config()[:consolidate_protocols]
    compilers = compilers() ++ if(consolidate_protocols?, do: [:protocols], else: [])
    shell.info("\nEnabled compilers: #{Enum.join(compilers, ", ")}")
    :ok
  end

  @impl true
  def run(args) do
    Mix.Project.get!()

    Mix.Task.run("loadpaths", args)

    {opts, _, _} = OptionParser.parse(args, switches: [erl_config: :string])
    load_erl_config(opts)

    {res, diagnostics} =
      Mix.Task.run("compile.all", args)
      |> List.wrap()
      |> Enum.map(
        &case &1 do
          :noop -> {:noop, []}
          {status, diagnostics} -> {status, diagnostics}
        end
      )
      |> Enum.reduce({:noop, []}, &merge_diagnostics/2)

    config = Mix.Project.config()

    # If we are in an umbrella project, now load paths from all children.
    if apps_paths = Mix.Project.apps_paths(config) do
      loaded_paths =
        (Mix.Tasks.Compile.All.project_apps(config) ++ Map.keys(apps_paths))
        |> Mix.AppLoader.load_apps(Mix.Dep.cached(), config, [], fn
          {_app, path}, acc -> if path, do: [path | acc], else: acc
        end)

      # We don't cache umbrella paths as we may write to them
      Code.prepend_paths(loaded_paths -- :code.get_path())
    end

    res =
      cond do
        "--no-compile" in args ->
          Mix.Task.reenable("compile")
          :noop

        Mix.Project.umbrella?(config) ->
          Mix.Compilers.Protocol.umbrella(args, res)

        true ->
          res
      end

    path = Mix.Project.consolidation_path(config)

    with {:ok, protocols} <- File.ls(path) do
      # We don't cache consolidation path as we may write to it
      Code.prepend_path(path)
      Enum.each(protocols, &load_protocol/1)
    end

    {res, diagnostics}
  end

  defp format(expression, args) do
    :io_lib.format(expression, args) |> IO.iodata_to_binary()
  end

  defp first_line(doc) do
    String.split(doc, "\n", parts: 2) |> hd() |> String.trim() |> String.trim_trailing(".")
  end

  defp merge_diagnostics({status1, diagnostics1}, {status2, diagnostics2}) do
    new_status =
      cond do
        status1 == :error or status2 == :error -> :error
        status1 == :ok or status2 == :ok -> :ok
        true -> :noop
      end

    {new_status, diagnostics1 ++ diagnostics2}
  end

  defp load_erl_config(opts) do
    if path = opts[:erl_config] do
      {:ok, terms} = :file.consult(path)
      Application.put_all_env(terms, persistent: true)
    end
  end

  @deprecated "Use Mix.Task.Compiler.manifests/0 instead"
  defdelegate manifests, to: Mix.Task.Compiler

  defp load_protocol(file) do
    case file do
      "Elixir." <> _ ->
        module = file |> Path.rootname() |> String.to_atom()
        :code.purge(module)
        :code.delete(module)

      _ ->
        :ok
    end
  end
end
