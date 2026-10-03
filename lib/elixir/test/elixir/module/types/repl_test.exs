# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team

Code.require_file("type_helper.exs", __DIR__)

defmodule Module.Types.ReplTest do
  use ExUnit.Case, async: true

  alias Module.Types.Repl

  test "defines aliases and checks subtyping" do
    assert {:ok, ["true"], %Repl{aliases: %{"pair" => _}}} =
             Repl.eval("""
             type pair = {boolean(), boolean} ;;
             {false, true} <= pair ;;
             """)
  end

  test "computes boolean operations" do
    assert {:ok, ["atom() or integer()", "none()", "integer()", "none()"], %Repl{}} =
             Repl.eval("""
             integer or atom ;;
             integer and not integer ;;
             integer and not atom ;;
             not integer and integer ;;
             """)
  end

  test "supports tuple syntax" do
    assert {:ok, ["{integer(), boolean()}", "{integer(), ...}", "true"], %Repl{}} =
             Repl.eval("""
             {integer, boolean} ;;
             {integer, ...} ;;
             {integer, boolean} <= {integer, ...} ;;
             """)
  end

  test "supports map syntax" do
    assert {:ok, ["%{foo: integer()}", "%{..., foo: integer()}", "%{atom() => integer()}"],
            %Repl{}} =
             Repl.eval("""
             %{foo: integer} ;;
             %{..., foo: integer} ;;
             %{atom() => integer()} ;;
             """)
  end

  test "supports cheatsheet constructors" do
    assert {:ok,
            [
              "fun()",
              "empty_map()",
              "empty_list()",
              "list(term())",
              "list(integer())",
              "empty_list() or non_empty_list(integer(), binary())",
              "non_empty_list(integer(), binary())",
              "(-> :ok)",
              "(binary(), binary() -> binary())",
              "%{fun() => binary()}",
              "%{list() => integer()}",
              "URI",
              "Foo.Bar"
            ], %Repl{}} =
             Repl.eval("""
             function() ;;
             empty_map() ;;
             empty_list() ;;
             list() ;;
             list(integer) ;;
             list(integer, binary) ;;
             non_empty_list(integer, binary) ;;
             (-> :ok) ;;
             (binary(), binary() -> binary()) ;;
             %{function() => binary()} ;;
             %{list() => integer()} ;;
             URI ;;
             Foo.Bar ;;
             """)
  end

  test "projects map value types" do
    assert {:ok,
            [
              "integer()",
              "nil or integer()",
              "nil or integer()",
              "nil or boolean() or integer()",
              "nil"
            ], %Repl{}} =
             Repl.eval("""
             %{foo: integer}[:foo] ;;
             %{atom() => integer()}[:foo] ;;
             %{atom() => integer()}[atom()] ;;
             %{foo: integer, bar: boolean}[atom()] ;;
             %{foo: integer}[:bar] ;;
             """)
  end

  test "selects required map fields" do
    assert {:ok, ["integer()", "boolean()", "integer()", "Foo.Bar"], %Repl{}} =
             Repl.eval("""
             %{foo: integer}.foo ;;
             %{..., foo: boolean}.foo ;;
             type t = %{foo: integer} ;;
             t.foo ;;
             Foo.Bar ;;
             """)

    assert {:error, message, %Repl{}} = Repl.eval("%{foo: integer}.bar ;;")
    assert message == "cannot select field :bar because it is not guaranteed on %{foo: integer()}"

    assert {:error, message, %Repl{}} = Repl.eval("%{foo: if_set(integer)}.foo ;;")
    assert message =~ "cannot select field :foo because it is not guaranteed"

    assert {:error, message, %Repl{}} = Repl.eval("%{atom() => integer()}.foo ;;")
    assert message =~ "cannot select field :foo because it is not guaranteed"
  end

  test "supports open map intersections" do
    assert {:ok, ["none()"], %Repl{}} =
             Repl.eval("%{foo: term()} and %{..., foo: term(), bar: term()} ;;")
  end

  test "accepts zero arity constructors with and without parentheses" do
    assert {:ok, ["true", "true", "true", "true"], %Repl{}} =
             Repl.eval("""
             integer = integer() ;;
             boolean = boolean() ;;
             term = term() ;;
             dynamic = dynamic() ;;
             """)
  end

  test "checks precision relation between gradual types" do
    assert {:ok, ["true", "true", "false", "false", "true", "true"], %Repl{}} =
             Repl.eval("""
             dynamic() <~ dynamic(integer()) ;;
             dynamic() <~= dynamic(integer()) ;;
             dynamic(integer()) <~ dynamic() ;;
             integer() <~ dynamic(integer()) ;;
             dynamic(integer()) <~ integer() ;;
             dynamic(atom()) <~ atom() ;;
             """)
  end

  test "checks consistent subtyping and compatibility relations" do
    assert {:ok, ["true", "true", "false", "true", "true", "false", "true", "false"], %Repl{}} =
             Repl.eval("""
             dynamic() <=~ integer() ;;
             dynamic(integer()) <=~ atom() ;;
             integer() <=~ dynamic(atom()) ;;
             integer() <=~ dynamic(number()) ;;
             integer() ~<= number() ;;
             number() ~<= integer() ;;
             dynamic() ~<= integer() ;;
             dynamic(integer()) ~<= atom() ;;
             """)
  end

  test "supports local type variables with bounds" do
    assert {:ok,
            [
              "{a, a}",
              "{a and integer(), a and integer()}",
              "true",
              "true",
              ":a"
            ], %Repl{}} =
             Repl.eval("""
             {a, a} when a: term() ;;
             {a, a} when a: integer() ;;
             ({a, a} when a: integer()) <= {integer(), integer()} ;;
             ({a, a} when a: term()) <= {term(), term()} ;;
             a ;;
             """)
  end

  test "tallies subtype constraints" do
    assert {:ok,
            [
              "[\n  a: a and integer()\n]",
              "[\n  a: integer()\n]",
              "no solutions",
              "[]",
              ":a"
            ], %Repl{}} =
             Repl.eval("""
             [ a <= integer() ] ;;
             [ a <= integer() ; integer() <= a ] ;;
             [ integer() <= atom() ] ;;
             [ integer() <= term() ] ;;
             a ;;
             """)
  end

  test "applies function types" do
    assert {:ok, ["integer()"], %Repl{}} =
             Repl.eval("(integer() -> boolean -> integer()) integer boolean() ;;")

    assert {:ok, ["integer()"], %Repl{}} =
             Repl.eval("((integer, integer) -> integer) (integer, integer) ;;")
  end

  test "checks pattern and guard precision" do
    assert {:ok, ["false", "true", "true", "false"], %Repl{}} =
             Repl.eval("""
             precise? {x, y} when x == y ;;
             precise? x when is_integer(x) ;;
             precise? x, y when x == :ok and y == :error ;;
             precise? [x | y] when is_integer(x) ;;
             """)
  end

  test "reports parse and type errors" do
    assert {:error, "cannot apply non-function type integer()", %Repl{}} =
             Repl.eval("integer boolean ;;")

    assert {:error, "bad function arity; expected one of [2]", %Repl{}} =
             Repl.eval("((integer, integer) -> integer) integer ;;")

    assert {:error, "cannot project non-map type integer()", %Repl{}} =
             Repl.eval("integer[:foo] ;;")

    assert {:error, "cannot select field :foo from non-map type integer()", %Repl{}} =
             Repl.eval("integer.foo ;;")

    assert {:error, "expected a pattern head after `precise?`", %Repl{}} =
             Repl.eval("precise? ;;")
  end
end
