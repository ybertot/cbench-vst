@rnd = float< ieee_32, ne >;
{b in [1, 2] /\ e in [1b-2, 1] ->
 ( rnd (rnd ( (b + (e * b)) + rnd ((b * b) / (b + (e * b)))) / 2)
   -
     b

    ) / (e * b) in [-127b-7,127b-7]}

