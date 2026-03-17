defmodule TypeSpecs.SmokeTest do
  import Module.Types.Descr

  @assert_type fun([integer()], integer()) |> intersection(fun([atom()], float()))
  def f(x), do: x

  @assert_type fun([atom([:ok])], atom([:ah]))
  def g(:ok), do: :a
end
