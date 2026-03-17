defmodule TypeSpecs.SmokeTest do
  import Module.Types.Descr

  @assert_type_form (integer() -> integer()) and (atom() -> float())
  def h(x), do: x

  @assert_type_form (integer() -> integer()) or ([atom()] -> boolean())
  def i(x), do: x
end
