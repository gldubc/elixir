defmodule TypeSpecs.SmokeTest do
  @define_type_form dyn_to_dyn: (dynamic() -> dynamic())
  @define_type_form bl: boolean()
  @assert_type_form dyn_to_dyn() and (bl() -> bl()) and (dynamic() -> %{..., integer() => float(), a: integer()})
  def negate(x) when is_integer(x), do: -x
  def negate(x) when is_boolean(x), do: not x
end
