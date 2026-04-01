defmodule TypeSpecs.SmokeTest do
  import Module.Types.Descr

  @assert_type fun([integer()], integer()) |> intersection(fun([boolean()], boolean()))
  def negate(x) when is_integer(x), do: -x
  def negate(x) when is_boolean(x), do: not x
end
