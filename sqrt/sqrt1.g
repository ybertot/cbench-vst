@rnd = float< ieee_32, ne >;
{a in [1,4] /\ b in [0,1] ->
 ( rnd (rnd ( (rnd (a + 1 / 3 * b)) + a /  (rnd (a + 1 / 3 * b))) / 2)
   -
   (((rnd (a + 1 / 3 * b)) + a / (rnd (a + 1 / 3 * b))) / 2)

    ) in ?}

