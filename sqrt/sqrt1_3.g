@rnd = float< ieee_32, ne >;
{b in [1, 2] /\ e in [0.9, 2] ->
 ( rnd (rnd ( (b + e * b) + rnd ((b * b) / (b + e * b))) / 2)
   -
    b

    )/(e * b) in [-0.5,0.5]}

