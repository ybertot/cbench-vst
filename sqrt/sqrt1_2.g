# This is the source for the proof of close_computation_from_gappa
@rnd = float< ieee_32, ne >;
{b in [1, 2] /\ e in [-1b-12, 1] ->
 ( rnd (rnd ( (b + (e * b)) + rnd ((b * b) / (b + (e * b)))) / 2)
   -
   ( ((b + (e * b)) + ((b * b) / (b + (e * b)))) / 2)

    ) in ?}

