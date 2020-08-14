requires "edsl.md"

module DSS-STORAGE
    imports EDSL

 // ### Vat
 // -------

    syntax Int ::= "#Vat.wards" "[" Int "]" [function]
 // --------------------------------------------------
    rule #Vat.wards[A] => #hashedLocation("Solidity", 0, A)

    syntax Int ::= "#Vat.can" "[" Int "][" Int "]" [function]
 // ---------------------------------------------------------
    rule #Vat.can[A][B] => #hashedLocation("Solidity", 1, A B)

    syntax Int ::= "#Vat.ilks" "[" Int "].Art" [function]
 // -----------------------------------------------------
    rule #Vat.ilks[Ilk].Art => #hashedLocation("Solidity", 2, Ilk) +Int 0

    syntax Int ::= "#Vat.ilks" "[" Int "].rate" [function]
 // ------------------------------------------------------
    rule #Vat.ilks[Ilk].rate => #hashedLocation("Solidity", 2, Ilk) +Int 1

    syntax Int ::= "#Vat.ilks" "[" Int "].spot" [function]
 // ------------------------------------------------------
    rule #Vat.ilks[Ilk].spot => #hashedLocation("Solidity", 2, Ilk) +Int 2

    syntax Int ::= "#Vat.ilks" "[" Int "].line" [function]
 // ------------------------------------------------------
    rule #Vat.ilks[Ilk].line => #hashedLocation("Solidity", 2, Ilk) +Int 3

    syntax Int ::= "#Vat.ilks" "[" Int "].dust" [function]
 // ------------------------------------------------------
    rule #Vat.ilks[Ilk].dust => #hashedLocation("Solidity", 2, Ilk) +Int 4

    syntax Int ::= "#Vat.urns" "[" Int "][" Int "].ink" [function]
 // --------------------------------------------------------------
    rule #Vat.urns[Ilk][Usr].ink => #hashedLocation("Solidity", 3, Ilk Usr)

    syntax Int ::= "#Vat.urns" "[" Int "][" Int "].art" [function]
 // --------------------------------------------------------------
    rule #Vat.urns[Ilk][Usr].art => #hashedLocation("Solidity", 3, Ilk Usr) +Int 1

    syntax Int ::= "#Vat.gem" "[" Int "][" Int "]" [function]
 // ---------------------------------------------------------
    rule #Vat.gem[Ilk][Usr] => #hashedLocation("Solidity", 4, Ilk Usr)

    syntax Int ::= "#Vat.dai" "[" Int "]" [function]
 // ------------------------------------------------
    rule #Vat.dai[A] => #hashedLocation("Solidity", 5, A)

    syntax Int ::= "#Vat.sin" "[" Int "]" [function]
 // ------------------------------------------------
    rule #Vat.sin[A] => #hashedLocation("Solidity", 6, A)

    syntax Int ::= "#Vat.debt" [function]
 // -------------------------------------
    rule #Vat.debt => 7

    syntax Int ::= "#Vat.vice" [function]
 // -------------------------------------
    rule #Vat.vice => 8

    syntax Int ::= "#Vat.Line" [function]
 // -------------------------------------
    rule #Vat.Line => 9

    syntax Int ::= "#Vat.live" [function]
 // -------------------------------------
    rule #Vat.live => 10

 // ### Dai
 // -------

    syntax Int ::= "#Dai.wards" "[" Int "]" [function]
 // --------------------------------------------------
    rule #Dai.wards[A] => #hashedLocation("Solidity", 0, A)

    syntax Int ::= "#Dai.totalSupply" [function]
 // --------------------------------------------
    rule #Dai.totalSupply => 1

    syntax Int ::= "#Dai.balanceOf" "[" Int "]" [function]
 // ------------------------------------------------------
    rule #Dai.balanceOf[A] => #hashedLocation("Solidity", 2, A)

    syntax Int ::= "#Dai.allowance" "[" Int "][" Int "]" [function]
 // ---------------------------------------------------------------
    rule #Dai.allowance[A][B] => #hashedLocation("Solidity", 3, A B)

    syntax Int ::= "#Dai.nonces" "[" Int "]" [function]
 // ---------------------------------------------------
    rule #Dai.nonces[A] => #hashedLocation("Solidity", 4, A)

    syntax Int ::= "#Dai.DOMAIN_SEPARATOR" [function]
 // -------------------------------------------------
    rule #Dai.DOMAIN_SEPARATOR => 5

 // ### Jug
 // -------

    syntax Int ::= "#Jug.wards" "[" Int "]" [function]
 // --------------------------------------------------
    rule #Jug.wards[A] => #hashedLocation("Solidity", 0, A)

    syntax Int ::= "#Jug.ilks" "[" Int "].duty" [function]
 // ------------------------------------------------------
    rule #Jug.ilks[Ilk].duty => #hashedLocation("Solidity", 1, Ilk) +Int 0

    syntax Int ::= "#Jug.ilks" "[" Int "].rho" [function]
 // -----------------------------------------------------
    rule #Jug.ilks[Ilk].rho => #hashedLocation("Solidity", 1, Ilk) +Int 1

    syntax Int ::= "#Jug.vat" [function]
 // ------------------------------------
    rule #Jug.vat => 2

    syntax Int ::= "#Jug.vow" [function]
 // ------------------------------------
    rule #Jug.vow => 3

    syntax Int ::= "#Jug.base" [function]
 // -------------------------------------
    rule #Jug.base => 4

 // ### Drip
 // --------

    syntax Int ::= "#Drip.wards" "[" Int "]" [function]
 // ---------------------------------------------------
    rule #Drip.wards[A] => #hashedLocation("Solidity", 0, A)

    syntax Int ::= "#Drip.ilks" "[" Int "].tax" [function]
 // ------------------------------------------------------
    rule #Drip.ilks[Ilk].tax => #hashedLocation("Solidity", 1, Ilk) +Int 0

    syntax Int ::= "#Drip.ilks" "[" Int "].rho" [function]
 // ------------------------------------------------------
    rule #Drip.ilks[Ilk].rho => #hashedLocation("Solidity", 1, Ilk) +Int 1

    syntax Int ::= "#Drip.vat" [function]
 // -------------------------------------
    rule #Drip.vat => 2

    syntax Int ::= "#Drip.vow" [function]
 // -------------------------------------
    rule #Drip.vow => 3

    syntax Int ::= "#Drip.repo" [function]
 // --------------------------------------
    rule #Drip.repo => 4

 // ### Vow
 // -------

    syntax Int ::= "#Vow.wards" "[" Int "]" [function]
 // --------------------------------------------------
    rule #Vow.wards[A] => #hashedLocation("Solidity", 0, A)

    syntax Int ::= "#Vow.vat" [function]
 // ------------------------------------
    rule #Vow.vat => 1

    syntax Int ::= "#Vow.flapper" [function]
 // ----------------------------------------
    rule #Vow.flapper => 2

    syntax Int ::= "#Vow.flopper" [function]
 // ----------------------------------------
    rule #Vow.flopper => 3

    syntax Int ::= "#Vow.sin" "[" Int "]" [function]
 // ------------------------------------------------
    rule #Vow.sin[A] => #hashedLocation("Solidity", 4, A)

    syntax Int ::= "#Vow.Sin" [function]
 // ------------------------------------
    rule #Vow.Sin => 5

    syntax Int ::= "#Vow.Ash" [function]
 // ------------------------------------
    rule #Vow.Ash => 6

    syntax Int ::= "#Vow.wait" [function]
 // -------------------------------------
    rule #Vow.wait => 7

    syntax Int ::= "#Vow.dump" [function]
 // -------------------------------------
    rule #Vow.dump => 8

    syntax Int ::= "#Vow.sump" [function]
 // -------------------------------------
    rule #Vow.sump => 9

    syntax Int ::= "#Vow.bump" [function]
 // -------------------------------------
    rule #Vow.bump => 10

    syntax Int ::= "#Vow.hump" [function]
 // -------------------------------------
    rule #Vow.hump => 11

    syntax Int ::= "#Vow.live" [function]
 // -------------------------------------
    rule #Vow.live => 12


 // ### Cat
 // -------

    syntax Int ::= "#Cat.wards" "[" Int "]" [function]
 // --------------------------------------------------
    rule #Cat.wards[A] => #hashedLocation("Solidity", 0, A)

    syntax Int ::= "#Cat.ilks" "[" Int "].flip" [function]
 // ------------------------------------------------------
    rule #Cat.ilks[Ilk].flip => #hashedLocation("Solidity", 1, Ilk) +Int 0

    syntax Int ::= "#Cat.ilks" "[" Int "].chop" [function]
 // ------------------------------------------------------
    rule #Cat.ilks[Ilk].chop => #hashedLocation("Solidity", 1, Ilk) +Int 1

    syntax Int ::= "#Cat.ilks" "[" Int "].lump" [function]
 // ------------------------------------------------------
    rule #Cat.ilks[Ilk].lump => #hashedLocation("Solidity", 1, Ilk) +Int 2

    syntax Int ::= "#Cat.live" [function]
 // -------------------------------------
    rule #Cat.live => 2

    syntax Int ::= "#Cat.vat" [function]
 // ------------------------------------
    rule #Cat.vat => 3

    syntax Int ::= "#Cat.vow" [function]
 // ------------------------------------
    rule #Cat.vow => 4

 // ### GemJoin
 // -----------

    syntax Int ::= "#GemJoin.wards" "[" Int "]"  [function]
 // -------------------------------------------------------
    rule #GemJoin.wards[A] => #hashedLocation("Solidity", 0, A)

    syntax Int ::= "#GemJoin.vat" [function]
 // ----------------------------------------
    rule #GemJoin.vat => 1

    syntax Int ::= "#GemJoin.ilk" [function]
 // ----------------------------------------
    rule #GemJoin.ilk => 2

    syntax Int ::= "#GemJoin.gem" [function]
 // ----------------------------------------
    rule #GemJoin.gem => 3

    syntax Int ::= "#GemJoin.dec" [function]
 // ----------------------------------------
    rule #GemJoin.dec => 4

    syntax Int ::= "#GemJoin.live" [function]
 // -----------------------------------------
    rule #GemJoin.live => 5

 // ### DaiJoin
 // -----------

    syntax Int ::= "#DaiJoin.wards" "[" Int "]"  [function]
 // -------------------------------------------------------
    rule #DaiJoin.wards[A] => #hashedLocation("Solidity", 0, A)

    syntax Int ::= "#DaiJoin.vat" [function]
 // ----------------------------------------
    rule #DaiJoin.vat => 1

    syntax Int ::= "#DaiJoin.dai" [function]
 // ----------------------------------------
    rule #DaiJoin.dai => 2

    syntax Int ::= "#DaiJoin.live" [function]
 // -----------------------------------------
    rule #DaiJoin.live => 3

 // ### Flip
 // --------

    syntax Int ::= "#Flipper.wards" "[" Int "]" [function]
 // ------------------------------------------------------
    rule #Flipper.wards[A] => #hashedLocation("Solidity", 0, A)

    syntax Int ::= "#Flipper.bids" "[" Int "].bid" [function]
 // ---------------------------------------------------------
    rule #Flipper.bids[N].bid => #hashedLocation("Solidity", 1, N) +Int 0

    syntax Int ::= "#Flipper.bids" "[" Int "].lot" [function]
 // ---------------------------------------------------------
    rule #Flipper.bids[N].lot => #hashedLocation("Solidity", 1, N) +Int 1

    syntax Int ::= "#Flipper.bids" "[" Int "].guy_tic_end" [function]
 // -----------------------------------------------------------------
    rule #Flipper.bids[N].guy_tic_end => #hashedLocation("Solidity", 1, N) +Int 2

    syntax Int ::= "#Flipper.bids" "[" Int "].usr" [function]
 // ---------------------------------------------------------
    rule #Flipper.bids[N].usr => #hashedLocation("Solidity", 1, N) +Int 3

    syntax Int ::= "#Flipper.bids" "[" Int "].gal" [function]
 // ---------------------------------------------------------
    rule #Flipper.bids[N].gal => #hashedLocation("Solidity", 1, N) +Int 4

    syntax Int ::= "#Flipper.bids" "[" Int "].tab" [function]
 // ---------------------------------------------------------
    rule #Flipper.bids[N].tab => #hashedLocation("Solidity", 1, N) +Int 5

    syntax Int ::= "#Flipper.vat" [function]
 // ----------------------------------------
    rule #Flipper.vat => 2

    syntax Int ::= "#Flipper.ilk" [function]
 // ----------------------------------------
    rule #Flipper.ilk => 3

    syntax Int ::= "#Flipper.beg" [function]
 // ----------------------------------------
    rule #Flipper.beg => 4

    syntax Int ::= "#Flipper.ttl_tau" [function]
 // --------------------------------------------
    rule #Flipper.ttl_tau => 5

    syntax Int ::= "#Flipper.kicks" [function]
 // ------------------------------------------
    rule #Flipper.kicks => 6


 // ### Flop
 // --------

    syntax Int ::= "#Flopper.wards" "[" Int "]" [function]
 // ------------------------------------------------------
    rule #Flopper.wards[A] => #hashedLocation("Solidity", 0, A)

    syntax Int ::= "#Flopper.bids" "[" Int "].bid" [function]
 // ---------------------------------------------------------
    rule #Flopper.bids[N].bid => #hashedLocation("Solidity", 1, N) +Int 0

    syntax Int ::= "#Flopper.bids" "[" Int "].lot" [function]
 // ---------------------------------------------------------
    rule #Flopper.bids[N].lot => #hashedLocation("Solidity", 1, N) +Int 1

    syntax Int ::= "#Flopper.bids" "[" Int "].guy_tic_end" [function]
 // -----------------------------------------------------------------
    rule #Flopper.bids[N].guy_tic_end => #hashedLocation("Solidity", 1, N) +Int 2

    syntax Int ::= "#Flopper.vat" [function]
 // ----------------------------------------
    rule #Flopper.vat => 2

    syntax Int ::= "#Flopper.gem" [function]
 // ----------------------------------------
    rule #Flopper.gem => 3

    syntax Int ::= "#Flopper.beg" [function]
 // ----------------------------------------
    rule #Flopper.beg => 4

    syntax Int ::= "#Flopper.pad" [function]
 // ----------------------------------------
    rule #Flopper.pad => 5

    syntax Int ::= "#Flopper.ttl_tau" [function]
 // --------------------------------------------
    rule #Flopper.ttl_tau => 6

    syntax Int ::= "#Flopper.kicks" [function]
 // ------------------------------------------
    rule #Flopper.kicks => 7

    syntax Int ::= "#Flopper.live" [function]
 // -----------------------------------------
    rule #Flopper.live => 8

    syntax Int ::= "#Flopper.vow" [function]
 // ----------------------------------------
    rule #Flopper.vow => 9

 // ### Flap
 // --------

    syntax Int ::= "#Flapper.wards" "[" Int "]" [function]
 // ------------------------------------------------------
    rule #Flapper.wards[A] => #hashedLocation("Solidity", 0, A)

    syntax Int ::= "#Flapper.bids" "[" Int "].bid" [function]
 // ---------------------------------------------------------
    rule #Flapper.bids[N].bid => #hashedLocation("Solidity", 1, N) +Int 0

    syntax Int ::= "#Flapper.bids" "[" Int "].lot" [function]
 // ---------------------------------------------------------
    rule #Flapper.bids[N].lot => #hashedLocation("Solidity", 1, N) +Int 1

    syntax Int ::= "#Flapper.bids" "[" Int "].guy_tic_end" [function]
 // -----------------------------------------------------------------
    rule #Flapper.bids[N].guy_tic_end => #hashedLocation("Solidity", 1, N) +Int 2

    syntax Int ::= "#Flapper.vat" [function]
 // ----------------------------------------
    rule #Flapper.vat => 2

    syntax Int ::= "#Flapper.gem" [function]
 // ----------------------------------------
    rule #Flapper.gem => 3

    syntax Int ::= "#Flapper.beg" [function]
 // ----------------------------------------
    rule #Flapper.beg => 4

    syntax Int ::= "#Flapper.ttl_tau" [function]
 // --------------------------------------------
    rule #Flapper.ttl_tau => 5

    syntax Int ::= "#Flapper.kicks" [function]
 // ------------------------------------------
    rule #Flapper.kicks => 6

    syntax Int ::= "#Flapper.live" [function]
 // -----------------------------------------
    rule #Flapper.live => 7

 // ### GemLike
 // -----------

    syntax Int ::= "#Gem.balances" "[" Int "]" [function]
 // -----------------------------------------------------
    rule #Gem.balances[A] => #hashedLocation("Solidity", 3, A)

    syntax Int ::= "#Gem.stopped" [function]
 // ----------------------------------------
    rule #Gem.stopped => 4

    syntax Int ::= "#Gem.allowance" "[" Int "][" Int "]" [function]
 // ---------------------------------------------------------------
    rule #Gem.allowance[A][B] => #hashedLocation("Solidity", 8, A B)

 // ### End
 // -------

    syntax Int ::= "#End.wards" "[" Int "]" [function]
 // --------------------------------------------------
    rule #End.wards[A] => #hashedLocation("Solidity", 0, A)

    syntax Int ::= "#End.vat" [function]
 // ------------------------------------
    rule #End.vat => 1

    syntax Int ::= "#End.cat" [function]
 // ------------------------------------
    rule #End.cat => 2

    syntax Int ::= "#End.vow" [function]
 // ------------------------------------
    rule #End.vow => 3

    syntax Int ::= "#End.pot" [function]
 // ------------------------------------
    rule #End.pot => 4

    syntax Int ::= "#End.spot" [function]
 // -------------------------------------
    rule #End.spot => 5

    syntax Int ::= "#End.live" [function]
 // -------------------------------------
    rule #End.live => 6

    syntax Int ::= "#End.when" [function]
 // -------------------------------------
    rule #End.when => 7

    syntax Int ::= "#End.wait" [function]
 // -------------------------------------
    rule #End.wait => 8

    syntax Int ::= "#End.debt" [function]
 // -------------------------------------
    rule #End.debt => 9

    syntax Int ::= "#End.tag" "[" Int "]" [function]
 // ------------------------------------------------
    rule #End.tag[Ilk] => #hashedLocation("Solidity", 10, Ilk)

    syntax Int ::= "#End.gap" "[" Int "]" [function]
 // ------------------------------------------------
    rule #End.gap[Ilk] => #hashedLocation("Solidity", 11, Ilk)

    syntax Int ::= "#End.Art" "[" Int "]" [function]
 // ------------------------------------------------
    rule #End.Art[Ilk] => #hashedLocation("Solidity", 12, Ilk)

    syntax Int ::= "#End.fix" "[" Int "]" [function]
 // ------------------------------------------------
    rule #End.fix[Ilk] => #hashedLocation("Solidity", 13, Ilk)

    syntax Int ::= "#End.bag" "[" Int "]" [function]
 // ------------------------------------------------
    rule #End.bag[Usr] => #hashedLocation("Solidity", 14, Usr)

    syntax Int ::= "#End.out" "[" Int "][" Int "]" [function]
 // ---------------------------------------------------------
    rule #End.out[Ilk][Usr] => #hashedLocation("Solidity", 15, Ilk Usr)

 // ### Pot
 // -------

    syntax Int ::= "#Pot.wards" "[" Int "]" [function]
 // --------------------------------------------------
    rule #Pot.wards[A] => #hashedLocation("Solidity", 0, A)

    syntax Int ::= "#Pot.pie" "[" Int "]" [function]
 // ------------------------------------------------
    rule #Pot.pie[Usr] => #hashedLocation("Solidity", 1, Usr)

    syntax Int ::= "#Pot.Pie" [function]
 // ------------------------------------
    rule #Pot.Pie => 2

    syntax Int ::= "#Pot.dsr" [function]
 // ------------------------------------
    rule #Pot.dsr => 3

    syntax Int ::= "#Pot.chi" [function]
 // ------------------------------------
    rule #Pot.chi => 4

    syntax Int ::= "#Pot.vat" [function]
 // ------------------------------------
    rule #Pot.vat => 5

    syntax Int ::= "#Pot.vow" [function]
 // ------------------------------------
    rule #Pot.vow => 6

    syntax Int ::= "#Pot.rho" [function]
 // ------------------------------------
    rule #Pot.rho => 7

    syntax Int ::= "#Pot.live" [function]
 // -------------------------------------
    rule #Pot.live => 8

 // ### DSToken
 // -----------

    syntax Int ::= "#DSToken.supply" [function]
 // -------------------------------------------
    rule #DSToken.supply => 0

    syntax Int ::= "#DSToken.balances" "[" Int "]" [function]
 // ---------------------------------------------------------
    rule #DSToken.balances[A] => #hashedLocation("Solidity", 1, A)

    syntax Int ::= "#DSToken.allowance" "[" Int "][" Int "]" [function]
 // -------------------------------------------------------------------
    rule #DSToken.allowance[A][B] => #hashedLocation("Solidity", 2, A B)

    syntax Int ::= "#DSToken.authority" [function]
 // ----------------------------------------------
    rule #DSToken.authority => 3

    syntax Int ::= "#DSToken.owner_stopped" [function]
 // --------------------------------------------------
    rule #DSToken.owner_stopped => 4

    syntax Int ::= "#DSToken.symbol" [function]
 // -------------------------------------------
    rule #DSToken.symbol => 5

    syntax Int ::= "#DSToken.decimals" [function]
 // ---------------------------------------------
    rule #DSToken.decimals => 6

 // ### DSValue
 // -----------

    syntax Int ::= "#DSValue.authority" [function]
 // ----------------------------------------------
    rule #DSValue.authority => 0

    syntax Int ::= "#DSValue.owner_has" [function]
 // ----------------------------------------------
    rule #DSValue.owner_has => 1

    syntax Int ::= "#DSValue.val" [function]
 // ----------------------------------------
    rule #DSValue.val => 2


 // ### Spotter
 // -----------

    syntax Int ::= "#Spotter.wards" "[" Int "]" [function]
 // ------------------------------------------------------
    rule #Spotter.wards[A] => #hashedLocation("Solidity", 0, A)

    syntax Int ::= "#Spotter.ilks" "[" Int "].pip" [function]
 // ---------------------------------------------------------
    rule #Spotter.ilks[Ilk].pip => #hashedLocation("Solidity", 1, Ilk) +Int 0

    syntax Int ::= "#Spotter.ilks" "[" Int "].mat" [function]
 // ---------------------------------------------------------
    rule #Spotter.ilks[Ilk].mat => #hashedLocation("Solidity", 1, Ilk) +Int 1

    syntax Int ::= "#Spotter.vat" [function]
 // ----------------------------------------
    rule #Spotter.vat => 2

    syntax Int ::= "#Spotter.par" [function]
 // ----------------------------------------
    rule #Spotter.par => 3

    syntax Int ::= "#Spotter.live" [function]
 // -----------------------------------------
    rule #Spotter.live => 4

endmodule
