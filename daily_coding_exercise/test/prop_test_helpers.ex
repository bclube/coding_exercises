defmodule PropTestHelpers do
  def bucket(value, bucket_size) when bucket_size > 0 do
    bottom = div(value, bucket_size) * bucket_size

    top = bottom + bucket_size

    [from: bottom, to: top]
  end
end
