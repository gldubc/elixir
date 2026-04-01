defmodule TypeSpecs.SmokeTest do
  @assert_type_form (dynamic() and integer() -> dynamic())
  def negate(x) when is_integer(x), do: -x
  def negate(x) when is_boolean(x), do: not x
end
