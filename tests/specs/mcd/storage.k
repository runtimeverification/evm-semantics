requires "edsl.md"

module DSS-STORAGE
    imports EDSL

 // ### Vat
 // -------

    syntax Int ::= "#Vat.wards" "[" Int "]" [function]
                 | "#Vat.can" "[" Int "][" Int "]" [function]
                 | "#Vat.ilks" "[" Int "].Art" [function]
                 | "#Vat.ilks" "[" Int "].rate" [function]
                 | "#Vat.ilks" "[" Int "].spot" [function]
                 | "#Vat.ilks" "[" Int "].line" [function]
                 | "#Vat.ilks" "[" Int "].dust" [function]
                 | "#Vat.urns" "[" Int "][" Int "].ink" [function]
                 | "#Vat.urns" "[" Int "][" Int "].art" [function]
                 | "#Vat.gem" "[" Int "][" Int "]" [function]
                 | "#Vat.dai" "[" Int "]" [function]
                 | "#Vat.sin" "[" Int "]" [function]
                 | "#Vat.debt" [function]
                 | "#Vat.vice" [function]
                 | "#Vat.Line" [function]
                 | "#Vat.live" [function]
 // --------------------------
    rule #Vat.wards[A]           => #hashedLocation("Solidity", 0, A)              [macro]
    rule #Vat.can[A][B]          => #hashedLocation("Solidity", 1, A B)            [macro]
    rule #Vat.ilks[Ilk].Art      => #hashedLocation("Solidity", 2, Ilk) +Int 0     [macro]
    rule #Vat.ilks[Ilk].rate     => #hashedLocation("Solidity", 2, Ilk) +Int 1     [macro]
    rule #Vat.ilks[Ilk].spot     => #hashedLocation("Solidity", 2, Ilk) +Int 2     [macro]
    rule #Vat.ilks[Ilk].line     => #hashedLocation("Solidity", 2, Ilk) +Int 3     [macro]
    rule #Vat.ilks[Ilk].dust     => #hashedLocation("Solidity", 2, Ilk) +Int 4     [macro]
    rule #Vat.urns[Ilk][Usr].ink => #hashedLocation("Solidity", 3, Ilk Usr)        [macro]
    rule #Vat.urns[Ilk][Usr].art => #hashedLocation("Solidity", 3, Ilk Usr) +Int 1 [macro]
    rule #Vat.gem[Ilk][Usr]      => #hashedLocation("Solidity", 4, Ilk Usr)        [macro]
    rule #Vat.dai[A]             => #hashedLocation("Solidity", 5, A)              [macro]
    rule #Vat.sin[A]             => #hashedLocation("Solidity", 6, A)              [macro]
    rule #Vat.debt               => 7                                              [macro]
    rule #Vat.vice               => 8                                              [macro]
    rule #Vat.Line               => 9                                              [macro]
    rule #Vat.live               => 10                                             [macro]

 // ### Dai
 // -------

    syntax Int ::= "#Dai.wards" "[" Int "]" [function]
                 | "#Dai.totalSupply" [function]
                 | "#Dai.balanceOf" "[" Int "]" [function]
                 | "#Dai.allowance" "[" Int "][" Int "]" [function]
                 | "#Dai.nonces" "[" Int "]" [function]
                 | "#Dai.DOMAIN_SEPARATOR" [function]
 // --------------------------------------
    rule #Dai.wards[A]         => #hashedLocation("Solidity", 0, A)   [macro]
    rule #Dai.totalSupply      => 1                                   [macro]
    rule #Dai.balanceOf[A]     => #hashedLocation("Solidity", 2, A)   [macro]
    rule #Dai.allowance[A][B]  => #hashedLocation("Solidity", 3, A B) [macro]
    rule #Dai.nonces[A]        => #hashedLocation("Solidity", 4, A)   [macro]
    rule #Dai.DOMAIN_SEPARATOR => 5                                   [macro]

 // ### Jug
 // -------

    syntax Int ::= "#Jug.wards" "[" Int "]" [function]
                 | "#Jug.ilks" "[" Int "].duty" [function]
                 | "#Jug.ilks" "[" Int "].rho" [function]
                 | "#Jug.vat" [function]
                 | "#Jug.vow" [function]
                 | "#Jug.base" [function]
 // --------------------------
    rule #Jug.wards[A]       => #hashedLocation("Solidity", 0, A)          [macro]
    rule #Jug.ilks[Ilk].duty => #hashedLocation("Solidity", 1, Ilk) +Int 0 [macro]
    rule #Jug.ilks[Ilk].rho  => #hashedLocation("Solidity", 1, Ilk) +Int 1 [macro]
    rule #Jug.vat            => 2                                          [macro]
    rule #Jug.vow            => 3                                          [macro]
    rule #Jug.base           => 4                                          [macro]

 // ### Drip
 // --------

    syntax Int ::= "#Drip.wards" "[" Int "]" [function]
                 | "#Drip.ilks" "[" Int "].tax" [function]
                 | "#Drip.ilks" "[" Int "].rho" [function]
                 | "#Drip.vat" [function]
                 | "#Drip.vow" [function]
                 | "#Drip.repo" [function]
 // ---------------------------
    rule #Drip.wards[A]      => #hashedLocation("Solidity", 0, A)          [macro]
    rule #Drip.ilks[Ilk].tax => #hashedLocation("Solidity", 1, Ilk) +Int 0 [macro]
    rule #Drip.ilks[Ilk].rho => #hashedLocation("Solidity", 1, Ilk) +Int 1 [macro]
    rule #Drip.vat           => 2                                          [macro]
    rule #Drip.vow           => 3                                          [macro]
    rule #Drip.repo          => 4                                          [macro]

 // ### Vow
 // -------

    syntax Int ::= "#Vow.wards" "[" Int "]" [function]
                 | "#Vow.vat" [function]
                 | "#Vow.flapper" [function]
                 | "#Vow.flopper" [function]
                 | "#Vow.sin" "[" Int "]" [function]
                 | "#Vow.Sin" [function]
                 | "#Vow.Ash" [function]
                 | "#Vow.wait" [function]
                 | "#Vow.dump" [function]
                 | "#Vow.sump" [function]
                 | "#Vow.bump" [function]
                 | "#Vow.hump" [function]
                 | "#Vow.live" [function]
 // --------------------------
    rule #Vow.wards[A] => #hashedLocation("Solidity", 0, A) [macro]
    rule #Vow.vat      => 1                                 [macro]
    rule #Vow.flapper  => 2                                 [macro]
    rule #Vow.flopper  => 3                                 [macro]
    rule #Vow.sin[A]   => #hashedLocation("Solidity", 4, A) [macro]
    rule #Vow.Sin      => 5                                 [macro]
    rule #Vow.Ash      => 6                                 [macro]
    rule #Vow.wait     => 7                                 [macro]
    rule #Vow.dump     => 8                                 [macro]
    rule #Vow.sump     => 9                                 [macro]
    rule #Vow.bump     => 10                                [macro]
    rule #Vow.hump     => 11                                [macro]
    rule #Vow.live     => 12                                [macro]

 // ### Cat
 // -------

    syntax Int ::= "#Cat.wards" "[" Int "]" [function]
                 | "#Cat.ilks" "[" Int "].flip" [function]
                 | "#Cat.ilks" "[" Int "].chop" [function]
                 | "#Cat.ilks" "[" Int "].lump" [function]
                 | "#Cat.live" [function]
                 | "#Cat.vat" [function]
                 | "#Cat.vow" [function]
 // -------------------------
    rule #Cat.wards[A]       => #hashedLocation("Solidity", 0, A)          [macro]
    rule #Cat.ilks[Ilk].flip => #hashedLocation("Solidity", 1, Ilk) +Int 0 [macro]
    rule #Cat.ilks[Ilk].chop => #hashedLocation("Solidity", 1, Ilk) +Int 1 [macro]
    rule #Cat.ilks[Ilk].lump => #hashedLocation("Solidity", 1, Ilk) +Int 2 [macro]
    rule #Cat.live           => 2                                          [macro]
    rule #Cat.vat            => 3                                          [macro]
    rule #Cat.vow            => 4                                          [macro]

 // ### GemJoin
 // -----------

    syntax Int ::= "#GemJoin.wards" "[" Int "]" [function]
                 | "#GemJoin.vat" [function]
                 | "#GemJoin.ilk" [function]
                 | "#GemJoin.gem" [function]
                 | "#GemJoin.dec" [function]
                 | "#GemJoin.live" [function]
 // ------------------------------
    rule #GemJoin.wards[A] => #hashedLocation("Solidity", 0, A) [macro]
    rule #GemJoin.vat      => 1                                 [macro]
    rule #GemJoin.ilk      => 2                                 [macro]
    rule #GemJoin.gem      => 3                                 [macro]
    rule #GemJoin.dec      => 4                                 [macro]
    rule #GemJoin.live     => 5                                 [macro]

 // ### DaiJoin
 // -----------

    syntax Int ::= "#DaiJoin.wards" "[" Int "]" [function]
                 | "#DaiJoin.vat" [function]
                 | "#DaiJoin.dai" [function]
                 | "#DaiJoin.live" [function]
 // ------------------------------
    rule #DaiJoin.wards[A] => #hashedLocation("Solidity", 0, A) [macro]
    rule #DaiJoin.vat      => 1                                 [macro]
    rule #DaiJoin.dai      => 2                                 [macro]
    rule #DaiJoin.live     => 3                                 [macro]

 // ### Flip
 // --------

    syntax Int ::= "#Flipper.wards" "[" Int "]" [function]
                 | "#Flipper.bids" "[" Int "].bid" [function]
                 | "#Flipper.bids" "[" Int "].lot" [function]
                 | "#Flipper.bids" "[" Int "].guy_tic_end" [function]
                 | "#Flipper.bids" "[" Int "].usr" [function]
                 | "#Flipper.bids" "[" Int "].gal" [function]
                 | "#Flipper.bids" "[" Int "].tab" [function]
                 | "#Flipper.vat" [function]
                 | "#Flipper.ilk" [function]
                 | "#Flipper.beg" [function]
                 | "#Flipper.ttl_tau" [function]
                 | "#Flipper.kicks" [function]
 // -------------------------------
    rule #Flipper.wards[A]            => #hashedLocation("Solidity", 0, A)        [macro]
    rule #Flipper.bids[N].bid         => #hashedLocation("Solidity", 1, N) +Int 0 [macro]
    rule #Flipper.bids[N].lot         => #hashedLocation("Solidity", 1, N) +Int 1 [macro]
    rule #Flipper.bids[N].guy_tic_end => #hashedLocation("Solidity", 1, N) +Int 2 [macro]
    rule #Flipper.bids[N].usr         => #hashedLocation("Solidity", 1, N) +Int 3 [macro]
    rule #Flipper.bids[N].gal         => #hashedLocation("Solidity", 1, N) +Int 4 [macro]
    rule #Flipper.bids[N].tab         => #hashedLocation("Solidity", 1, N) +Int 5 [macro]
    rule #Flipper.vat                 => 2                                        [macro]
    rule #Flipper.ilk                 => 3                                        [macro]
    rule #Flipper.beg                 => 4                                        [macro]
    rule #Flipper.ttl_tau             => 5                                        [macro]
    rule #Flipper.kicks               => 6                                        [macro]

 // ### Flop
 // --------

    syntax Int ::= "#Flopper.wards" "[" Int "]" [function]
                 | "#Flopper.bids" "[" Int "].bid" [function]
                 | "#Flopper.bids" "[" Int "].lot" [function]
                 | "#Flopper.bids" "[" Int "].guy_tic_end" [function]
                 | "#Flopper.vat" [function]
                 | "#Flopper.gem" [function]
                 | "#Flopper.beg" [function]
                 | "#Flopper.pad" [function]
                 | "#Flopper.ttl_tau" [function]
                 | "#Flopper.kicks" [function]
                 | "#Flopper.live" [function]
                 | "#Flopper.vow" [function]
 // -----------------------------
    rule #Flopper.wards[A]            => #hashedLocation("Solidity", 0, A)        [macro]
    rule #Flopper.bids[N].bid         => #hashedLocation("Solidity", 1, N) +Int 0 [macro]
    rule #Flopper.bids[N].lot         => #hashedLocation("Solidity", 1, N) +Int 1 [macro]
    rule #Flopper.bids[N].guy_tic_end => #hashedLocation("Solidity", 1, N) +Int 2 [macro]
    rule #Flopper.vat                 => 2                                        [macro]
    rule #Flopper.gem                 => 3                                        [macro]
    rule #Flopper.beg                 => 4                                        [macro]
    rule #Flopper.pad                 => 5                                        [macro]
    rule #Flopper.ttl_tau             => 6                                        [macro]
    rule #Flopper.kicks               => 7                                        [macro]
    rule #Flopper.live                => 8                                        [macro]
    rule #Flopper.vow                 => 9                                        [macro]

 // ### Flap
 // --------

    syntax Int ::= "#Flapper.wards" "[" Int "]" [function]
                 | "#Flapper.bids" "[" Int "].bid" [function]
                 | "#Flapper.bids" "[" Int "].lot" [function]
                 | "#Flapper.bids" "[" Int "].guy_tic_end" [function]
                 | "#Flapper.vat" [function]
                 | "#Flapper.gem" [function]
                 | "#Flapper.beg" [function]
                 | "#Flapper.ttl_tau" [function]
                 | "#Flapper.kicks" [function]
                 | "#Flapper.live" [function]
 // ------------------------------
    rule #Flapper.wards[A]            => #hashedLocation("Solidity", 0, A)        [macro]
    rule #Flapper.bids[N].bid         => #hashedLocation("Solidity", 1, N) +Int 0 [macro]
    rule #Flapper.bids[N].lot         => #hashedLocation("Solidity", 1, N) +Int 1 [macro]
    rule #Flapper.bids[N].guy_tic_end => #hashedLocation("Solidity", 1, N) +Int 2 [macro]
    rule #Flapper.vat                 => 2                                        [macro]
    rule #Flapper.gem                 => 3                                        [macro]
    rule #Flapper.beg                 => 4                                        [macro]
    rule #Flapper.ttl_tau             => 5                                        [macro]
    rule #Flapper.kicks               => 6                                        [macro]
    rule #Flapper.live                => 7                                        [macro]

 // ### GemLike
 // -----------

    syntax Int ::= "#Gem.balances" "[" Int "]" [function]
                 | "#Gem.stopped" [function]
                 | "#Gem.allowance" "[" Int "][" Int "]" [function]
 // ----------------------------------------------------
    rule #Gem.balances[A]     => #hashedLocation("Solidity", 3, A)   [macro]
    rule #Gem.stopped         => 4                                   [macro]
    rule #Gem.allowance[A][B] => #hashedLocation("Solidity", 8, A B) [macro]

 // ### End
 // -------

    syntax Int ::= "#End.wards" "[" Int "]" [function]
                 | "#End.vat" [function]
                 | "#End.cat" [function]
                 | "#End.vow" [function]
                 | "#End.pot" [function]
                 | "#End.spot" [function]
                 | "#End.live" [function]
                 | "#End.when" [function]
                 | "#End.wait" [function]
                 | "#End.debt" [function]
                 | "#End.tag" "[" Int "]" [function]
                 | "#End.gap" "[" Int "]" [function]
                 | "#End.Art" "[" Int "]" [function]
                 | "#End.fix" "[" Int "]" [function]
                 | "#End.bag" "[" Int "]" [function]
                 | "#End.out" "[" Int "][" Int "]" [function]
 // ----------------------------------------------
    rule #End.wards[A]      => #hashedLocation("Solidity", 0, A)        [macro]
    rule #End.vat           => 1                                        [macro]
    rule #End.cat           => 2                                        [macro]
    rule #End.vow           => 3                                        [macro]
    rule #End.pot           => 4                                        [macro]
    rule #End.spot          => 5                                        [macro]
    rule #End.live          => 6                                        [macro]
    rule #End.when          => 7                                        [macro]
    rule #End.wait          => 8                                        [macro]
    rule #End.debt          => 9                                        [macro]
    rule #End.tag[Ilk]      => #hashedLocation("Solidity", 10, Ilk)     [macro]
    rule #End.gap[Ilk]      => #hashedLocation("Solidity", 11, Ilk)     [macro]
    rule #End.Art[Ilk]      => #hashedLocation("Solidity", 12, Ilk)     [macro]
    rule #End.fix[Ilk]      => #hashedLocation("Solidity", 13, Ilk)     [macro]
    rule #End.bag[Usr]      => #hashedLocation("Solidity", 14, Usr)     [macro]
    rule #End.out[Ilk][Usr] => #hashedLocation("Solidity", 15, Ilk Usr) [macro]

 // ### Pot
 // -------

    syntax Int ::= "#Pot.wards" "[" Int "]" [function]
                 | "#Pot.pie" "[" Int "]" [function]
                 | "#Pot.Pie" [function]
                 | "#Pot.dsr" [function]
                 | "#Pot.chi" [function]
                 | "#Pot.vat" [function]
                 | "#Pot.vow" [function]
                 | "#Pot.rho" [function]
                 | "#Pot.live" [function]
 // --------------------------
    rule #Pot.wards[A] => #hashedLocation("Solidity", 0, A)   [macro]
    rule #Pot.pie[Usr] => #hashedLocation("Solidity", 1, Usr) [macro]
    rule #Pot.Pie      => 2                                   [macro]
    rule #Pot.dsr      => 3                                   [macro]
    rule #Pot.chi      => 4                                   [macro]
    rule #Pot.vat      => 5                                   [macro]
    rule #Pot.vow      => 6                                   [macro]
    rule #Pot.rho      => 7                                   [macro]
    rule #Pot.live     => 8                                   [macro]

 // ### DSToken
 // -----------

    syntax Int ::= "#DSToken.supply" [function]
                 | "#DSToken.balances" "[" Int "]" [function]
                 | "#DSToken.allowance" "[" Int "][" Int "]" [function]
                 | "#DSToken.authority" [function]
                 | "#DSToken.owner_stopped" [function]
                 | "#DSToken.symbol" [function]
                 | "#DSToken.decimals" [function]
 // ----------------------------------
    rule #DSToken.supply          => 0                                   [macro]
    rule #DSToken.balances[A]     => #hashedLocation("Solidity", 1, A)   [macro]
    rule #DSToken.allowance[A][B] => #hashedLocation("Solidity", 2, A B) [macro]
    rule #DSToken.authority       => 3                                   [macro]
    rule #DSToken.owner_stopped   => 4                                   [macro]
    rule #DSToken.symbol          => 5                                   [macro]
    rule #DSToken.decimals        => 6                                   [macro]

 // ### DSValue
 // -----------

    syntax Int ::= "#DSValue.authority" [function]
                 | "#DSValue.owner_has" [function]
                 | "#DSValue.val" [function]
 // -----------------------------
    rule #DSValue.authority => 0 [macro]
    rule #DSValue.owner_has => 1 [macro]
    rule #DSValue.val       => 2 [macro]

 // ### Spotter
 // -----------

    syntax Int ::= "#Spotter.wards" "[" Int "]" [function]
                 | "#Spotter.ilks" "[" Int "].pip" [function]
                 | "#Spotter.ilks" "[" Int "].mat" [function]
                 | "#Spotter.vat" [function]
                 | "#Spotter.par" [function]
                 | "#Spotter.live" [function]
 // ------------------------------
    rule #Spotter.wards[A]      => #hashedLocation("Solidity", 0, A)          [macro]
    rule #Spotter.ilks[Ilk].pip => #hashedLocation("Solidity", 1, Ilk) +Int 0 [macro]
    rule #Spotter.ilks[Ilk].mat => #hashedLocation("Solidity", 1, Ilk) +Int 1 [macro]
    rule #Spotter.vat           => 2                                          [macro]
    rule #Spotter.par           => 3                                          [macro]
    rule #Spotter.live          => 4                                          [macro]

endmodule
