@rnd = float< ieee_32, ne >;
{b in [1, 2] ->
 ( rnd (rnd ( b + rnd ((b * b) / b)) / 2)
   -
   ( (b + ((b * b) / b)) / 2)

    ) in [-3b-23,3b-23]}

