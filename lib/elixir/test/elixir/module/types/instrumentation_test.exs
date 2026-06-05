# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team

Code.require_file("type_helper.exs", __DIR__)

defmodule Module.Types.InstrumentationTest do
  use ExUnit.Case, async: false

  import TypeHelper

  @moduletag :tmp_dir

  @env_vars [
    "ELIXIR_GUARD_EXACTNESS_DIR",
    "ELIXIR_GUARD_EXACTNESS_PROJECT",
    "ELIXIR_GUARD_EXACTNESS_REPO_ROOT",
    "ELIXIR_GUARD_EXACTNESS_RUN_ID"
  ]

  setup %{tmp_dir: tmp_dir} do
    previous = Map.new(@env_vars, &{&1, System.get_env(&1)})

    System.put_env("ELIXIR_GUARD_EXACTNESS_DIR", tmp_dir)
    System.put_env("ELIXIR_GUARD_EXACTNESS_PROJECT", "TypesTest")
    System.put_env("ELIXIR_GUARD_EXACTNESS_REPO_ROOT", File.cwd!())
    System.put_env("ELIXIR_GUARD_EXACTNESS_RUN_ID", "test-run")

    on_exit(fn ->
      for {key, value} <- previous do
        if is_nil(value), do: System.delete_env(key), else: System.put_env(key, value)
      end
    end)

    :ok
  end

  test "emits exact guard rows", %{tmp_dir: tmp_dir} do
    assert precise?([x], is_integer(x))

    [row] = rows(tmp_dir)
    assert row["project"] == "TypesTest"
    assert row["guard_count"] == 1
    assert row["exact"] == true
    assert hd(row["patterns"]) =~ "x"
    assert hd(row["guards"]) =~ "integer"
    assert row["possible_arg_types"] == row["sure_arg_types"]
  end

  test "emits exact negated guard rows", %{tmp_dir: tmp_dir} do
    assert precise?([x], not is_integer(x))

    [row] = rows(tmp_dir)
    assert row["guard_count"] == 1
    assert row["exact"] == true
    assert hd(row["guards"]) =~ "integer"
  end

  test "emits inexact guard rows", %{tmp_dir: tmp_dir} do
    refute precise?([x, y], x == y)

    [row] = rows(tmp_dir)
    assert row["guard_count"] == 1
    assert row["exact"] == false
    assert row["sure_arg_types"] == [~S(#{}), ~S(#{})]
  end

  test "emits guardless pattern rows", %{tmp_dir: tmp_dir} do
    x = {:x, [version: make_ref(), line: __ENV__.line], nil}
    assert TypeHelper.__precise__?([x], [])

    [row] = rows(tmp_dir)
    assert row["guard_count"] == 0
    assert row["guards"] == []
    assert row["exact"] == true
  end

  test "emits generator rows", %{tmp_dir: tmp_dir} do
    typecheck!(
      (
        for x when is_integer(x) <- [1], do: x
      )
    )

    assert Enum.any?(rows(tmp_dir), &(&1["site_kind"] == "for"))
  end

  test "emits with rows", %{tmp_dir: tmp_dir} do
    typecheck!(
      (
        with x when is_integer(x) <- 1 do
          x
        end
      )
    )

    assert Enum.any?(rows(tmp_dir), &(&1["site_kind"] == "with"))
  end

  defp rows(tmp_dir) do
    tmp_dir
    |> Path.join("*.jsonl")
    |> Path.wildcard()
    |> Enum.flat_map(fn path ->
      path
      |> File.read!()
      |> String.split("\n", trim: true)
      |> Enum.map(&:json.decode/1)
    end)
  end
end
