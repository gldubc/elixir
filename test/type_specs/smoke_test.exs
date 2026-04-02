defmodule TypeSpecs.SmokeTest do
  @define_type_form dyn_to_dyn: (dynamic() -> dynamic())
  @define_type_form bl: boolean()
  @define_type_form tu: {atom(), integer()}
  
  @assert_type_form dyn_to_dyn() and (bl() -> bl()) and (dynamic() -> %{..., integer() => float(), a: integer()})
  def negate(x) when is_integer(x), do: -x
  def negate(x) when is_boolean(x), do: not x

  @assert_type_form (integer() -> tu())
  def to_tuple(x) when is_integer(x), do: {:ok, x}

  @assert_type_form (integer() -> {integer()})
  def to_tuple1(x) when is_integer(x), do: {x}

  @assert_type_form (integer() -> {atom(), integer(), boolean()})
  def to_tuple3(x) when is_integer(x), do: {:ok, x, true}
end
