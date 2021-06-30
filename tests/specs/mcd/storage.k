requires "edsl.md"

module DSS-STORAGE
    imports EDSL

 // ### Vat
 // -------

    syntax Int ::= "#Vat.wards" "[" Int "]"
                 | "#Vat.can" "[" Int "][" Int "]"
                 | "#Vat.ilks" "[" Int "].Art"
                 | "#Vat.ilks" "[" Int "].rate"
                 | "#Vat.ilks" "[" Int "].spot"
                 | "#Vat.ilks" "[" Int "].line"
                 | "#Vat.ilks" "[" Int "].dust"
                 | "#Vat.urns" "[" Int "][" Int "].ink"
                 | "#Vat.urns" "[" Int "][" Int "].art"
                 | "#Vat.gem" "[" Int "][" Int "]"
                 | "#Vat.dai" "[" Int "]"
                 | "#Vat.sin" "[" Int "]"
                 | "#Vat.debt"
                 | "#Vat.vice"
                 | "#Vat.Line"
                 | "#Vat.live"
 // --------------------------
    rule #Vat.wards[A]           => #hashedLocation("Solidity", 0, A)              [macro]
    rule #Vat.can[A][B]          => #hashedLocation("Solidity", 1, A B)            [macro]
    rule #Vat.ilks[ILK].Art      => #hashedLocation("Solidity", 2, ILK) +Int 0     [macro]
    rule #Vat.ilks[ILK].rate     => #hashedLocation("Solidity", 2, ILK) +Int 1     [macro]
    rule #Vat.ilks[ILK].spot     => #hashedLocation("Solidity", 2, ILK) +Int 2     [macro]
    rule #Vat.ilks[ILK].line     => #hashedLocation("Solidity", 2, ILK) +Int 3     [macro]
    rule #Vat.ilks[ILK].dust     => #hashedLocation("Solidity", 2, ILK) +Int 4     [macro]
    rule #Vat.urns[ILK][USR].ink => #hashedLocation("Solidity", 3, ILK USR)        [macro]
    rule #Vat.urns[ILK][USR].art => #hashedLocation("Solidity", 3, ILK USR) +Int 1 [macro]
    rule #Vat.gem[ILK][USR]      => #hashedLocation("Solidity", 4, ILK USR)        [macro]
    rule #Vat.dai[A]             => #hashedLocation("Solidity", 5, A)              [macro]
    rule #Vat.sin[A]             => #hashedLocation("Solidity", 6, A)              [macro]
    rule #Vat.debt               => 7                                              [macro]
    rule #Vat.vice               => 8                                              [macro]
    rule #Vat.Line               => 9                                              [macro]
    rule #Vat.live               => 10                                             [macro]

 // ### Dai
 // -------

    syntax Int ::= "#Dai.wards" "[" Int "]"
                 | "#Dai.totalSupply"
                 | "#Dai.balanceOf" "[" Int "]"
                 | "#Dai.allowance" "[" Int "][" Int "]"
                 | "#Dai.nonces" "[" Int "]"
                 | "#Dai.DOMAIN_SEPARATOR"
 // --------------------------------------
    rule #Dai.wards[A]         => #hashedLocation("Solidity", 0, A)   [macro]
    rule #Dai.totalSupply      => 1                                   [macro]
    rule #Dai.balanceOf[A]     => #hashedLocation("Solidity", 2, A)   [macro]
    rule #Dai.allowance[A][B]  => #hashedLocation("Solidity", 3, A B) [macro]
    rule #Dai.nonces[A]        => #hashedLocation("Solidity", 4, A)   [macro]
    rule #Dai.DOMAIN_SEPARATOR => 5                                   [macro]

 // ### Jug
 // -------

    syntax Int ::= "#Jug.wards" "[" Int "]"
                 | "#Jug.ilks" "[" Int "].duty"
                 | "#Jug.ilks" "[" Int "].rho"
                 | "#Jug.vat"
                 | "#Jug.vow"
                 | "#Jug.base"
 // --------------------------
    rule #Jug.wards[A]       => #hashedLocation("Solidity", 0, A)          [macro]
    rule #Jug.ilks[ILK].duty => #hashedLocation("Solidity", 1, ILK) +Int 0 [macro]
    rule #Jug.ilks[ILK].rho  => #hashedLocation("Solidity", 1, ILK) +Int 1 [macro]
    rule #Jug.vat            => 2                                          [macro]
    rule #Jug.vow            => 3                                          [macro]
    rule #Jug.base           => 4                                          [macro]

 // ### Drip
 // --------

    syntax Int ::= "#Drip.wards" "[" Int "]"
                 | "#Drip.ilks" "[" Int "].tax"
                 | "#Drip.ilks" "[" Int "].rho"
                 | "#Drip.vat"
                 | "#Drip.vow"
                 | "#Drip.repo"
 // ---------------------------
    rule #Drip.wards[A]      => #hashedLocation("Solidity", 0, A)          [macro]
    rule #Drip.ilks[ILK].tax => #hashedLocation("Solidity", 1, ILK) +Int 0 [macro]
    rule #Drip.ilks[ILK].rho => #hashedLocation("Solidity", 1, ILK) +Int 1 [macro]
    rule #Drip.vat           => 2                                          [macro]
    rule #Drip.vow           => 3                                          [macro]
    rule #Drip.repo          => 4                                          [macro]

 // ### Vow
 // -------

    syntax Int ::= "#Vow.wards" "[" Int "]"
                 | "#Vow.vat"
                 | "#Vow.flapper"
                 | "#Vow.flopper"
                 | "#Vow.sin" "[" Int "]"
                 | "#Vow.Sin"
                 | "#Vow.Ash"
                 | "#Vow.wait"
                 | "#Vow.dump"
                 | "#Vow.sump"
                 | "#Vow.bump"
                 | "#Vow.hump"
                 | "#Vow.live"
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

    syntax Int ::= "#Cat.wards" "[" Int "]"
                 | "#Cat.ilks" "[" Int "].flip"
                 | "#Cat.ilks" "[" Int "].chop"
                 | "#Cat.ilks" "[" Int "].lump"
                 | "#Cat.live"
                 | "#Cat.vat"
                 | "#Cat.vow"
 // -------------------------
    rule #Cat.wards[A]       => #hashedLocation("Solidity", 0, A)          [macro]
    rule #Cat.ilks[ILK].flip => #hashedLocation("Solidity", 1, ILK) +Int 0 [macro]
    rule #Cat.ilks[ILK].chop => #hashedLocation("Solidity", 1, ILK) +Int 1 [macro]
    rule #Cat.ilks[ILK].lump => #hashedLocation("Solidity", 1, ILK) +Int 2 [macro]
    rule #Cat.live           => 2                                          [macro]
    rule #Cat.vat            => 3                                          [macro]
    rule #Cat.vow            => 4                                          [macro]

 // ### GemJoin
 // -----------

    syntax Int ::= "#GemJoin.wards" "[" Int "]"
                 | "#GemJoin.vat"
                 | "#GemJoin.ilk"
                 | "#GemJoin.gem"
                 | "#GemJoin.dec"
                 | "#GemJoin.live"
 // ------------------------------
    rule #GemJoin.wards[A] => #hashedLocation("Solidity", 0, A) [macro]
    rule #GemJoin.vat      => 1                                 [macro]
    rule #GemJoin.ilk      => 2                                 [macro]
    rule #GemJoin.gem      => 3                                 [macro]
    rule #GemJoin.dec      => 4                                 [macro]
    rule #GemJoin.live     => 5                                 [macro]

 // ### DaiJoin
 // -----------

    syntax Int ::= "#DaiJoin.wards" "[" Int "]"
                 | "#DaiJoin.vat"
                 | "#DaiJoin.dai"
                 | "#DaiJoin.live"
 // ------------------------------
    rule #DaiJoin.wards[A] => #hashedLocation("Solidity", 0, A) [macro]
    rule #DaiJoin.vat      => 1                                 [macro]
    rule #DaiJoin.dai      => 2                                 [macro]
    rule #DaiJoin.live     => 3                                 [macro]

 // ### Flip
 // --------

    syntax Int ::= "#Flipper.wards" "[" Int "]"
                 | "#Flipper.bids" "[" Int "].bid"
                 | "#Flipper.bids" "[" Int "].lot"
                 | "#Flipper.bids" "[" Int "].guy_tic_end"
                 | "#Flipper.bids" "[" Int "].usr"
                 | "#Flipper.bids" "[" Int "].gal"
                 | "#Flipper.bids" "[" Int "].tab"
                 | "#Flipper.vat"
                 | "#Flipper.ilk"
                 | "#Flipper.beg"
                 | "#Flipper.ttl_tau"
                 | "#Flipper.kicks"
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

    syntax Int ::= "#Flopper.wards" "[" Int "]"
                 | "#Flopper.bids" "[" Int "].bid"
                 | "#Flopper.bids" "[" Int "].lot"
                 | "#Flopper.bids" "[" Int "].guy_tic_end"
                 | "#Flopper.vat"
                 | "#Flopper.gem"
                 | "#Flopper.beg"
                 | "#Flopper.pad"
                 | "#Flopper.ttl_tau"
                 | "#Flopper.kicks"
                 | "#Flopper.live"
                 | "#Flopper.vow"
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

    syntax Int ::= "#Flapper.wards" "[" Int "]"
                 | "#Flapper.bids" "[" Int "].bid"
                 | "#Flapper.bids" "[" Int "].lot"
                 | "#Flapper.bids" "[" Int "].guy_tic_end"
                 | "#Flapper.vat"
                 | "#Flapper.gem"
                 | "#Flapper.beg"
                 | "#Flapper.ttl_tau"
                 | "#Flapper.kicks"
                 | "#Flapper.live"
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

    syntax Int ::= "#Gem.balances" "[" Int "]"
                 | "#Gem.stopped"
                 | "#Gem.allowance" "[" Int "][" Int "]"
 // ----------------------------------------------------
    rule #Gem.balances[A]     => #hashedLocation("Solidity", 3, A)   [macro]
    rule #Gem.stopped         => 4                                   [macro]
    rule #Gem.allowance[A][B] => #hashedLocation("Solidity", 8, A B) [macro]

 // ### End
 // -------

    syntax Int ::= "#End.wards" "[" Int "]"
                 | "#End.vat"
                 | "#End.cat"
                 | "#End.vow"
                 | "#End.pot"
                 | "#End.spot"
                 | "#End.live"
                 | "#End.when"
                 | "#End.wait"
                 | "#End.debt"
                 | "#End.tag" "[" Int "]"
                 | "#End.gap" "[" Int "]"
                 | "#End.Art" "[" Int "]"
                 | "#End.fix" "[" Int "]"
                 | "#End.bag" "[" Int "]"
                 | "#End.out" "[" Int "][" Int "]"
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
    rule #End.tag[ILK]      => #hashedLocation("Solidity", 10, ILK)     [macro]
    rule #End.gap[ILK]      => #hashedLocation("Solidity", 11, ILK)     [macro]
    rule #End.Art[ILK]      => #hashedLocation("Solidity", 12, ILK)     [macro]
    rule #End.fix[ILK]      => #hashedLocation("Solidity", 13, ILK)     [macro]
    rule #End.bag[USR]      => #hashedLocation("Solidity", 14, USR)     [macro]
    rule #End.out[ILK][USR] => #hashedLocation("Solidity", 15, ILK USR) [macro]

 // ### Pot
 // -------

    syntax Int ::= "#Pot.wards" "[" Int "]"
                 | "#Pot.pie" "[" Int "]"
                 | "#Pot.Pie"
                 | "#Pot.dsr"
                 | "#Pot.chi"
                 | "#Pot.vat"
                 | "#Pot.vow"
                 | "#Pot.rho"
                 | "#Pot.live"
 // --------------------------
    rule #Pot.wards[A] => #hashedLocation("Solidity", 0, A)   [macro]
    rule #Pot.pie[USR] => #hashedLocation("Solidity", 1, USR) [macro]
    rule #Pot.Pie      => 2                                   [macro]
    rule #Pot.dsr      => 3                                   [macro]
    rule #Pot.chi      => 4                                   [macro]
    rule #Pot.vat      => 5                                   [macro]
    rule #Pot.vow      => 6                                   [macro]
    rule #Pot.rho      => 7                                   [macro]
    rule #Pot.live     => 8                                   [macro]

 // ### DSToken
 // -----------

    syntax Int ::= "#DSToken.supply"
                 | "#DSToken.balances" "[" Int "]"
                 | "#DSToken.allowance" "[" Int "][" Int "]"
                 | "#DSToken.authority"
                 | "#DSToken.owner_stopped"
                 | "#DSToken.symbol"
                 | "#DSToken.decimals"
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

    syntax Int ::= "#DSValue.authority"
                 | "#DSValue.owner_has"
                 | "#DSValue.val"
 // -----------------------------
    rule #DSValue.authority => 0 [macro]
    rule #DSValue.owner_has => 1 [macro]
    rule #DSValue.val       => 2 [macro]

 // ### Spotter
 // -----------

    syntax Int ::= "#Spotter.wards" "[" Int "]"
                 | "#Spotter.ilks" "[" Int "].pip"
                 | "#Spotter.ilks" "[" Int "].mat"
                 | "#Spotter.vat"
                 | "#Spotter.par"
                 | "#Spotter.live"
 // ------------------------------
    rule #Spotter.wards[A]      => #hashedLocation("Solidity", 0, A)          [macro]
    rule #Spotter.ilks[ILK].pip => #hashedLocation("Solidity", 1, ILK) +Int 0 [macro]
    rule #Spotter.ilks[ILK].mat => #hashedLocation("Solidity", 1, ILK) +Int 1 [macro]
    rule #Spotter.vat           => 2                                          [macro]
    rule #Spotter.par           => 3                                          [macro]
    rule #Spotter.live          => 4                                          [macro]

endmodule
