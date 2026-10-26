# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team

Code.require_file("type_helper.exs", __DIR__)

defmodule Module.Types.TallyTest do
  use ExUnit.Case, async: false

  import Module.Types.Descr

  describe "bounds" do
    test "solves trivial, closed, and rigid constraints" do
      x = var(:x)
      y = var(:y)

      assert tally([]) == [%{}]
      assert tally([{integer(), term()}]) == [%{}]
      assert tally([{integer(), atom()}]) == []
      assert tally([{x, y}], [x, y]) == []
    end

    test "computes principal upper and lower bounds" do
      x = var(:x)
      rigid = var(:rigid)

      upper = tally([{x, rigid}], [rigid])
      lower = tally([{rigid, x}], [rigid])

      assert_solution(upper, %{x => opt_intersection(x, rigid)})
      assert_solution(lower, %{x => opt_union(x, rigid)})
      assert_sound(upper, [{x, rigid}])
      assert_sound(lower, [{rigid, x}])
    end

    test "keeps residual variables in principal solutions" do
      x = var(:x)
      y = var(:y)

      solutions = tally([{x, y}])

      assert_solution(solutions, %{x => opt_intersection(x, y)})
      assert MapSet.subset?(vars(Map.fetch!(hd(solutions), x)), MapSet.new([x, y]))
      assert_sound(solutions, [{x, y}])
    end

    test "merges and propagates bounds" do
      x = var(:x)
      number = opt_union(integer(), float())
      constraints = [{integer(), x}, {x, number}]

      solutions = tally(constraints)

      assert_solution(solutions, %{
        x => opt_intersection(opt_union(x, integer()), number)
      })

      assert_sound(solutions, constraints)

      a = var(:a)
      b = var(:b)
      assert tally([{a, b}, {b, integer()}, {atom(), a}]) == []
    end
  end

  describe "constructors" do
    test "uses function argument contravariance and result covariance" do
      x = var(:x)
      y = var(:y)
      argument = var(:argument)
      result = var(:result)
      constraints = [{fun([x], y), fun([argument], result)}]

      solutions = tally(constraints, [argument, result])

      assert_solution(solutions, %{
        x => opt_union(x, argument),
        y => opt_intersection(y, result)
      })

      assert_sound(solutions, constraints)
    end

    test "branches across tuple coordinates" do
      x = var(:x)
      y = var(:y)
      first = var(:first)
      second = var(:second)
      constraints = [{tuple([x, y]), tuple([first, second])}]

      solutions = tally(constraints, [first, second])

      assert length(solutions) == 3
      assert_solution(solutions, %{x => none()})
      assert_solution(solutions, %{y => none()})

      assert_solution(solutions, %{
        x => opt_intersection(x, first),
        y => opt_intersection(y, second)
      })

      assert_sound(solutions, constraints)
    end

    test "preserves homogeneous list alternatives" do
      x = var(:x)

      constraints = [
        {non_empty_list(x),
         opt_union(non_empty_list(atom([true])), non_empty_list(atom([false])))}
      ]

      solutions = tally(constraints)

      assert length(solutions) == 2
      assert_solution(solutions, %{x => opt_intersection(x, atom([true]))})
      assert_solution(solutions, %{x => opt_intersection(x, atom([false]))})
      assert_sound(solutions, constraints)
    end

    test "normalizes required and optional map fields" do
      x = var(:x)
      rigid = var(:rigid)

      required = [{closed_map(value: x), closed_map(value: rigid)}]
      optional = [{closed_map(value: if_set(x)), closed_map(value: if_set(rigid))}]

      required_solutions = tally(required, [rigid])
      optional_solutions = tally(optional, [rigid])

      assert_solution(required_solutions, %{x => opt_intersection(x, rigid)})
      assert_solution(optional_solutions, %{x => opt_intersection(x, rigid)})
      assert_sound(required_solutions, required)
      assert_sound(optional_solutions, optional)
    end
  end

  describe "recursive solving" do
    @tag timeout: 2_000
    test "ties contractive equations into recursive descriptors" do
      x = var(:x)
      constraints = [{x, tuple([x])}]

      assert [%{^x => solution}] = solutions = tally(constraints)
      assert match?({_, _, _}, solution)
      assert_sound(solutions, constraints)
    end

    @tag timeout: 2_000
    test "validates recursive solutions with residual variables" do
      i = var(:i)
      ia = var(:ia)

      # Solutions need ia >= i >= {ia}, a recursive type with a residual variable
      constraints = [{i, ia}, {tuple([ia]), i}]
      assert_sound(tally(constraints), constraints)

      constraints = [{i, ia}, {opt_union(atom([:bump]), tuple([fun([], ia)])), i}]
      assert_sound(tally(constraints), constraints)
    end
  end

  describe "one solution" do
    test "answers [] exactly when tally/2 does" do
      x = var(:x)
      y = var(:y)

      satisfiable = [
        [],
        [{integer(), term()}],
        [{x, integer()}],
        [{tuple([x, y]), tuple([atom([:a]), integer()])}],
        [{x, opt_union(atom([:a]), integer())}, {atom([:a]), x}]
      ]

      unsatisfiable = [
        [{integer(), atom()}],
        [{atom([:a]), x}, {x, atom([:b])}],
        [{tuple([x, integer()]), tuple([atom([:a]), integer()])}, {atom([:b]), x}]
      ]

      for constraints <- satisfiable do
        assert [_] = solutions = tally_first(constraints)
        assert tally(constraints) != []
        assert_sound(solutions, constraints)
      end

      for constraints <- unsatisfiable do
        assert tally_first(constraints) == []
        assert tally(constraints) == []
      end
    end

    test "returns one solution where tally/2 returns several" do
      [x, y, u, v] = Enum.map([:x, :y, :u, :v], &var/1)
      # {term, term} <= {x, y} or {u, v}: the choice of the summand gives several solutions
      constraints = [{tuple([term(), term()]), opt_union(tuple([x, y]), tuple([u, v]))}]
      assert length(tally(constraints)) > 1
      assert [_] = solutions = tally_first(constraints)
      assert_sound(solutions, constraints)
    end

    @tag timeout: 2_000
    test "solves recursive constraints" do
      x = var(:x)
      constraints = [{x, tuple([x])}]
      assert [%{^x => solution}] = solutions = tally_first(constraints)
      assert match?({_, _, _}, solution)
      assert_sound(solutions, constraints)
    end
  end

  describe "mutually recursive solutions" do
    # The solutions of all the variables of a saturated set are built together, as one
    # system of recursive equations.
    test "a cycle of variables" do
      finishes(fn ->
        vars = for i <- 1..6, do: var(:"x#{i}")

        constraints =
          vars
          |> Enum.with_index()
          |> Enum.map(fn {x, i} ->
            {opt_union(atom([:z]), tuple([Enum.at(vars, rem(i + 1, 6))])), x}
          end)

        assert [solution | _] = solutions = tally(constraints)
        assert_sound(solutions, constraints)

        # By symmetry, once the residual variables are none(), every variable is the
        # same type: :z, {:z}, {{:z}}, ... as a recursive type.
        ground = fn t -> substitute(t, Map.new(vars(t), &{&1, none()})) end
        [first | rest] = Enum.map(vars, &(solution |> Map.fetch!(&1) |> ground.()))
        refute empty?(first)
        assert Enum.all?(rest, &equal?(&1, first))
      end)
    end

    test "variables whose bounds are other variables and recursive types" do
      finishes(fn ->
        [x, y, z] = Enum.map([:x, :y, :z], &var/1)

        constraints = [
          {opt_union(atom([:a]), tuple([y])), x},
          {opt_union(atom([:b]), tuple([x, z])), y},
          {z, atom([:c])},
          {atom([:c]), z}
        ]

        solutions = tally(constraints)
        assert_sound(solutions, constraints)
        assert_sound(tally_first(constraints), constraints)
      end)
    end

    test "variables that occur in each other through function types" do
      # a >= :bump | {:run, job(b)} and b >= :tick | {:run, job(a)}, where the variable
      # occurs in the codomain of an argument of job.
      finishes(fn ->
        [a, b] = Enum.map([:a, :b], &var/1)
        job_a = process_fun(tuple([]), none(), a, term())
        job_b = process_fun(tuple([]), none(), b, term())

        constraints = [
          {opt_union(atom([:bump]), tuple([atom([:run]), job_b])), a},
          {opt_union(atom([:tick]), tuple([atom([:run]), job_a])), b}
        ]

        assert [_ | _] = solutions = tally(constraints)
        assert_sound(solutions, constraints)
        assert [_] = tally_first(constraints) |> tap(&assert_sound(&1, constraints))
      end)
    end
  end

  # Each computation is stopped after one second, or when its heap goes beyond 50M
  # words. Recursive nodes are interned in the process that builds them, so each test
  # builds its types, solves and checks within that computation.
  describe "recursive solutions below constructors" do
    test "a variable in a Boolean combination below a constructor" do
      # The recursive solution is a node whose generator substitutes the node for x in
      # {x or :b}: the union is substituted lazily, in a node of its own.
      x = var(:x)
      constraints = [{tuple([opt_union(x, atom([:b]))]), x}]
      finishes(fn -> assert_sound(tally(constraints), constraints) end)
    end

    test "a recursive solution through function types" do
      # Solutions need ia >= i >= :bump | {:run, job(ia)}, where ia occurs in the
      # codomain of an argument of job.
      [oa, ia, i, res] = Enum.map([:oa, :ia, :i, :res], &var/1)
      job = process_fun(tuple([]), oa, ia, term())
      worker = opt_union(atom([:bump]), tuple([atom([:run]), job]))
      constraints = [{job, process_fun(tuple([]), none(), i, res)}, {worker, i}]
      finishes(fn -> assert_sound(tally(constraints), constraints) end)
    end

    test "validating solutions with recursive types through function types" do
      # solve/1 finds the expected solution at once; valid_solution?/2 must compare
      # copies of the recursive types, which are named after their substitution.
      finishes(fn ->
        worker =
          recursive(%{
            W: fn recur ->
              job = process_fun(tuple([]), atom([:bump]), recur.(:W), term())
              atom([:bump]) |> bare_union(tuple([atom([:run]), job]))
            end
          })
          |> Map.fetch!(:W)
          |> to_descr()

        [o_spawn, i_spawn, p1, p2, o_app, i_app, res] =
          Enum.map([:o_spawn, :i_spawn, :p1, :p2, :o_app, :i_app, :res], &var/1)

        constraints = [
          {o_spawn, worker},
          {worker, i_spawn},
          {opt_intersection(i_spawn, tuple([atom([:run]), term()])), tuple([p1, p2])},
          {p1, atom([:run])},
          {o_app, o_spawn},
          {i_spawn, i_app},
          {p2, process_fun(tuple([]), o_app, i_app, res)},
          {opt_intersection(i_spawn, atom([:bump])), atom([:bump])}
        ]

        solutions = tally(constraints)
        assert_sound(solutions, constraints)
        assert Enum.any?(solutions, &equal?(Map.fetch!(&1, i_app), worker))
      end)
    end

    test "a recursive solution through function types, with bracket variables" do
      # As above, but both annotations of job are variables, and the application of
      # job adds the variables o_app and i_app between them and the worker.
      [oa, ia, o_spawn, i_spawn, p1, p2, o_app, i_app, res] =
        Enum.map([:oa, :ia, :o_spawn, :i_spawn, :p1, :p2, :o_app, :i_app, :res], &var/1)

      job = process_fun(tuple([]), oa, ia, term())
      worker = opt_union(atom([:bump]), tuple([atom([:run]), job]))

      constraints = [
        {o_spawn, worker},
        {worker, i_spawn},
        {opt_intersection(i_spawn, tuple([atom([:run]), term()])), tuple([p1, p2])},
        {o_app, o_spawn},
        {i_spawn, i_app},
        {p2, process_fun(tuple([]), o_app, i_app, res)}
      ]

      finishes(fn -> assert_sound(tally(constraints), constraints) end)
    end
  end

  describe "validation" do
    test "rejects malformed, gradual, and non-variable inputs" do
      x = var(:x)

      assert_raise ArgumentError, ~r/constraint/, fn -> tally([integer()]) end
      assert_raise ArgumentError, ~r/static types/, fn -> tally([{dynamic(), x}]) end
      assert_raise ArgumentError, ~r/type variable/, fn -> tally([{x, term()}], [integer()]) end
      assert_raise ArgumentError, ~r/MapSet or list/, fn -> tally([{x, term()}], :fixed) end
    end
  end

  # A function type with three arguments, as a checker for message-passing processes
  # encodes a function of domain s and codomain t whose body sends messages of type o
  # and receives messages of type i.
  defp process_fun(s, o, i, t) do
    fun([opt_union(s, port()), fun([o], port()), fun([], i)], t)
  end

  defp finishes(fun) do
    task =
      Task.async(fn ->
        Process.flag(:max_heap_size, %{size: 50_000_000, kill: true, error_logger: false})
        fun.()
      end)

    Process.unlink(task.pid)

    case Task.yield(task, 1_000) || Task.shutdown(task, :brutal_kill) do
      {:ok, result} -> result
      {:exit, {%ExUnit.AssertionError{} = error, stacktrace}} -> reraise error, stacktrace
      _ -> flunk("operation did not finish")
    end
  end

  defp assert_solution(solutions, expected) do
    assert Enum.any?(solutions, fn solution ->
             map_size(solution) == map_size(expected) and
               Enum.all?(expected, fn {variable, expected_type} ->
                 case Map.fetch(solution, variable) do
                   {:ok, actual_type} -> equal?(actual_type, expected_type)
                   :error -> false
                 end
               end)
           end),
           "expected a semantically equivalent solution"
  end

  defp assert_sound(solutions, constraints) do
    assert solutions != []

    for solution <- solutions, {left, right} <- constraints do
      assert subtype?(substitute(left, solution), substitute(right, solution))
    end
  end
end
