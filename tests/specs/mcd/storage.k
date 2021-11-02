requires "edsl.md"

module DSS-STORAGE
    imports EDSL

 // ### Vat
 // -------

    syntax Int ::= "#Vat.wards" "[" Int "]"             [macro]
                 | "#Vat.can" "[" Int "][" Int "]"      [macro]
                 | "#Vat.ilks" "[" Int "].Art"          [macro]
                 | "#Vat.ilks" "[" Int "].rate"         [macro]
                 | "#Vat.ilks" "[" Int "].spot"         [macro]
                 | "#Vat.ilks" "[" Int "].line"         [macro]
                 | "#Vat.ilks" "[" Int "].dust"         [macro]
                 | "#Vat.urns" "[" Int "][" Int "].ink" [macro]
                 | "#Vat.urns" "[" Int "][" Int "].art" [macro]
                 | "#Vat.gem" "[" Int "][" Int "]"      [macro]
                 | "#Vat.dai" "[" Int "]"               [macro]
                 | "#Vat.sin" "[" Int "]"               [macro]
                 | "#Vat.debt"                          [macro]
                 | "#Vat.vice"                          [macro]
                 | "#Vat.Line"                          [macro]
                 | "#Vat.live"                          [macro]
 // -----------------------------------------------------------
    rule #Vat.wards[A]           => #hashedLocation("Solidity", 0, A)
    rule #Vat.can[A][B]          => #hashedLocation("Solidity", 1, A B)
    rule #Vat.ilks[ILK].Art      => #hashedLocation("Solidity", 2, ILK) +Int 0
    rule #Vat.ilks[ILK].rate     => #hashedLocation("Solidity", 2, ILK) +Int 1
    rule #Vat.ilks[ILK].spot     => #hashedLocation("Solidity", 2, ILK) +Int 2
    rule #Vat.ilks[ILK].line     => #hashedLocation("Solidity", 2, ILK) +Int 3
    rule #Vat.ilks[ILK].dust     => #hashedLocation("Solidity", 2, ILK) +Int 4
    rule #Vat.urns[ILK][USR].ink => #hashedLocation("Solidity", 3, ILK USR)
    rule #Vat.urns[ILK][USR].art => #hashedLocation("Solidity", 3, ILK USR) +Int 1
    rule #Vat.gem[ILK][USR]      => #hashedLocation("Solidity", 4, ILK USR)
    rule #Vat.dai[A]             => #hashedLocation("Solidity", 5, A)
    rule #Vat.sin[A]             => #hashedLocation("Solidity", 6, A)
    rule #Vat.debt               => 7
    rule #Vat.vice               => 8
    rule #Vat.Line               => 9
    rule #Vat.live               => 10

 // ### Dai
 // -------

    syntax Int ::= "#Dai.wards" "[" Int "]"              [macro]
                 | "#Dai.totalSupply"                    [macro]
                 | "#Dai.balanceOf" "[" Int "]"          [macro]
                 | "#Dai.allowance" "[" Int "][" Int "]" [macro]
                 | "#Dai.nonces" "[" Int "]"             [macro]
                 | "#Dai.DOMAIN_SEPARATOR"               [macro]
 // ------------------------------------------------------------
    rule #Dai.wards[A]         => #hashedLocation("Solidity", 0, A)
    rule #Dai.totalSupply      => 1
    rule #Dai.balanceOf[A]     => #hashedLocation("Solidity", 2, A)
    rule #Dai.allowance[A][B]  => #hashedLocation("Solidity", 3, A B)
    rule #Dai.nonces[A]        => #hashedLocation("Solidity", 4, A)
    rule #Dai.DOMAIN_SEPARATOR => 5

 // ### Jug
 // -------

    syntax Int ::= "#Jug.wards" "[" Int "]"     [macro]
                 | "#Jug.ilks" "[" Int "].duty" [macro]
                 | "#Jug.ilks" "[" Int "].rho"  [macro]
                 | "#Jug.vat"                   [macro]
                 | "#Jug.vow"                   [macro]
                 | "#Jug.base"                  [macro]
 // ---------------------------------------------------
    rule #Jug.wards[A]       => #hashedLocation("Solidity", 0, A)
    rule #Jug.ilks[ILK].duty => #hashedLocation("Solidity", 1, ILK) +Int 0
    rule #Jug.ilks[ILK].rho  => #hashedLocation("Solidity", 1, ILK) +Int 1
    rule #Jug.vat            => 2
    rule #Jug.vow            => 3
    rule #Jug.base           => 4

 // ### Drip
 // --------

    syntax Int ::= "#Drip.wards" "[" Int "]"    [macro]
                 | "#Drip.ilks" "[" Int "].tax" [macro]
                 | "#Drip.ilks" "[" Int "].rho" [macro]
                 | "#Drip.vat"                  [macro]
                 | "#Drip.vow"                  [macro]
                 | "#Drip.repo"                 [macro]
 // ---------------------------------------------------
    rule #Drip.wards[A]      => #hashedLocation("Solidity", 0, A)
    rule #Drip.ilks[ILK].tax => #hashedLocation("Solidity", 1, ILK) +Int 0
    rule #Drip.ilks[ILK].rho => #hashedLocation("Solidity", 1, ILK) +Int 1
    rule #Drip.vat           => 2
    rule #Drip.vow           => 3
    rule #Drip.repo          => 4

 // ### Vow
 // -------

    syntax Int ::= "#Vow.wards" "[" Int "]" [macro]
                 | "#Vow.vat"               [macro]
                 | "#Vow.flapper"           [macro]
                 | "#Vow.flopper"           [macro]
                 | "#Vow.sin" "[" Int "]"   [macro]
                 | "#Vow.Sin"               [macro]
                 | "#Vow.Ash"               [macro]
                 | "#Vow.wait"              [macro]
                 | "#Vow.dump"              [macro]
                 | "#Vow.sump"              [macro]
                 | "#Vow.bump"              [macro]
                 | "#Vow.hump"              [macro]
                 | "#Vow.live"              [macro]
 // -----------------------------------------------
    rule #Vow.wards[A] => #hashedLocation("Solidity", 0, A)
    rule #Vow.vat      => 1
    rule #Vow.flapper  => 2
    rule #Vow.flopper  => 3
    rule #Vow.sin[A]   => #hashedLocation("Solidity", 4, A)
    rule #Vow.Sin      => 5
    rule #Vow.Ash      => 6
    rule #Vow.wait     => 7
    rule #Vow.dump     => 8
    rule #Vow.sump     => 9
    rule #Vow.bump     => 10
    rule #Vow.hump     => 11
    rule #Vow.live     => 12

 // ### Cat
 // -------

    syntax Int ::= "#Cat.wards" "[" Int "]"     [macro]
                 | "#Cat.ilks" "[" Int "].flip" [macro]
                 | "#Cat.ilks" "[" Int "].chop" [macro]
                 | "#Cat.ilks" "[" Int "].lump" [macro]
                 | "#Cat.live"                  [macro]
                 | "#Cat.vat"                   [macro]
                 | "#Cat.vow"                   [macro]
 // ---------------------------------------------------
    rule #Cat.wards[A]       => #hashedLocation("Solidity", 0, A)
    rule #Cat.ilks[ILK].flip => #hashedLocation("Solidity", 1, ILK) +Int 0
    rule #Cat.ilks[ILK].chop => #hashedLocation("Solidity", 1, ILK) +Int 1
    rule #Cat.ilks[ILK].lump => #hashedLocation("Solidity", 1, ILK) +Int 2
    rule #Cat.live           => 2
    rule #Cat.vat            => 3
    rule #Cat.vow            => 4

 // ### GemJoin
 // -----------

    syntax Int ::= "#GemJoin.wards" "[" Int "]" [macro]
                 | "#GemJoin.vat"               [macro]
                 | "#GemJoin.ilk"               [macro]
                 | "#GemJoin.gem"               [macro]
                 | "#GemJoin.dec"               [macro]
                 | "#GemJoin.live"              [macro]
 // ---------------------------------------------------
    rule #GemJoin.wards[A] => #hashedLocation("Solidity", 0, A)
    rule #GemJoin.vat      => 1
    rule #GemJoin.ilk      => 2
    rule #GemJoin.gem      => 3
    rule #GemJoin.dec      => 4
    rule #GemJoin.live     => 5

 // ### DaiJoin
 // -----------

    syntax Int ::= "#DaiJoin.wards" "[" Int "]" [macro]
                 | "#DaiJoin.vat"               [macro]
                 | "#DaiJoin.dai"               [macro]
                 | "#DaiJoin.live"              [macro]
 // ---------------------------------------------------
    rule #DaiJoin.wards[A] => #hashedLocation("Solidity", 0, A)
    rule #DaiJoin.vat      => 1
    rule #DaiJoin.dai      => 2
    rule #DaiJoin.live     => 3

 // ### Flip
 // --------

    syntax Int ::= "#Flipper.wards" "[" Int "]"            [macro]
                 | "#Flipper.bids" "[" Int "].bid"         [macro]
                 | "#Flipper.bids" "[" Int "].lot"         [macro]
                 | "#Flipper.bids" "[" Int "].guy_tic_end" [macro]
                 | "#Flipper.bids" "[" Int "].usr"         [macro]
                 | "#Flipper.bids" "[" Int "].gal"         [macro]
                 | "#Flipper.bids" "[" Int "].tab"         [macro]
                 | "#Flipper.vat"                          [macro]
                 | "#Flipper.ilk"                          [macro]
                 | "#Flipper.beg"                          [macro]
                 | "#Flipper.ttl_tau"                      [macro]
                 | "#Flipper.kicks"                        [macro]
 // --------------------------------------------------------------
    rule #Flipper.wards[A]            => #hashedLocation("Solidity", 0, A)
    rule #Flipper.bids[N].bid         => #hashedLocation("Solidity", 1, N) +Int 0
    rule #Flipper.bids[N].lot         => #hashedLocation("Solidity", 1, N) +Int 1
    rule #Flipper.bids[N].guy_tic_end => #hashedLocation("Solidity", 1, N) +Int 2
    rule #Flipper.bids[N].usr         => #hashedLocation("Solidity", 1, N) +Int 3
    rule #Flipper.bids[N].gal         => #hashedLocation("Solidity", 1, N) +Int 4
    rule #Flipper.bids[N].tab         => #hashedLocation("Solidity", 1, N) +Int 5
    rule #Flipper.vat                 => 2
    rule #Flipper.ilk                 => 3
    rule #Flipper.beg                 => 4
    rule #Flipper.ttl_tau             => 5
    rule #Flipper.kicks               => 6

 // ### Flop
 // --------

    syntax Int ::= "#Flopper.wards" "[" Int "]"            [macro]
                 | "#Flopper.bids" "[" Int "].bid"         [macro]
                 | "#Flopper.bids" "[" Int "].lot"         [macro]
                 | "#Flopper.bids" "[" Int "].guy_tic_end" [macro]
                 | "#Flopper.vat"                          [macro]
                 | "#Flopper.gem"                          [macro]
                 | "#Flopper.beg"                          [macro]
                 | "#Flopper.pad"                          [macro]
                 | "#Flopper.ttl_tau"                      [macro]
                 | "#Flopper.kicks"                        [macro]
                 | "#Flopper.live"                         [macro]
                 | "#Flopper.vow"                          [macro]
 // --------------------------------------------------------------
    rule #Flopper.wards[A]            => #hashedLocation("Solidity", 0, A)
    rule #Flopper.bids[N].bid         => #hashedLocation("Solidity", 1, N) +Int 0
    rule #Flopper.bids[N].lot         => #hashedLocation("Solidity", 1, N) +Int 1
    rule #Flopper.bids[N].guy_tic_end => #hashedLocation("Solidity", 1, N) +Int 2
    rule #Flopper.vat                 => 2
    rule #Flopper.gem                 => 3
    rule #Flopper.beg                 => 4
    rule #Flopper.pad                 => 5
    rule #Flopper.ttl_tau             => 6
    rule #Flopper.kicks               => 7
    rule #Flopper.live                => 8
    rule #Flopper.vow                 => 9

 // ### Flap
 // --------

    syntax Int ::= "#Flapper.wards" "[" Int "]"            [macro]
                 | "#Flapper.bids" "[" Int "].bid"         [macro]
                 | "#Flapper.bids" "[" Int "].lot"         [macro]
                 | "#Flapper.bids" "[" Int "].guy_tic_end" [macro]
                 | "#Flapper.vat"                          [macro]
                 | "#Flapper.gem"                          [macro]
                 | "#Flapper.beg"                          [macro]
                 | "#Flapper.ttl_tau"                      [macro]
                 | "#Flapper.kicks"                        [macro]
                 | "#Flapper.live"                         [macro]
 // --------------------------------------------------------------
    rule #Flapper.wards[A]            => #hashedLocation("Solidity", 0, A)
    rule #Flapper.bids[N].bid         => #hashedLocation("Solidity", 1, N) +Int 0
    rule #Flapper.bids[N].lot         => #hashedLocation("Solidity", 1, N) +Int 1
    rule #Flapper.bids[N].guy_tic_end => #hashedLocation("Solidity", 1, N) +Int 2
    rule #Flapper.vat                 => 2
    rule #Flapper.gem                 => 3
    rule #Flapper.beg                 => 4
    rule #Flapper.ttl_tau             => 5
    rule #Flapper.kicks               => 6
    rule #Flapper.live                => 7

 // ### GemLike
 // -----------

    syntax Int ::= "#Gem.balances" "[" Int "]"           [macro]
                 | "#Gem.stopped"                        [macro]
                 | "#Gem.allowance" "[" Int "][" Int "]" [macro]
 // ------------------------------------------------------------
    rule #Gem.balances[A]     => #hashedLocation("Solidity", 3, A)
    rule #Gem.stopped         => 4
    rule #Gem.allowance[A][B] => #hashedLocation("Solidity", 8, A B)

 // ### End
 // -------

    syntax Int ::= "#End.wards" "[" Int "]"        [macro]
                 | "#End.vat"                      [macro]
                 | "#End.cat"                      [macro]
                 | "#End.vow"                      [macro]
                 | "#End.pot"                      [macro]
                 | "#End.spot"                     [macro]
                 | "#End.live"                     [macro]
                 | "#End.when"                     [macro]
                 | "#End.wait"                     [macro]
                 | "#End.debt"                     [macro]
                 | "#End.tag" "[" Int "]"          [macro]
                 | "#End.gap" "[" Int "]"          [macro]
                 | "#End.Art" "[" Int "]"          [macro]
                 | "#End.fix" "[" Int "]"          [macro]
                 | "#End.bag" "[" Int "]"          [macro]
                 | "#End.out" "[" Int "][" Int "]" [macro]
 // ------------------------------------------------------
    rule #End.wards[A]      => #hashedLocation("Solidity", 0, A)
    rule #End.vat           => 1
    rule #End.cat           => 2
    rule #End.vow           => 3
    rule #End.pot           => 4
    rule #End.spot          => 5
    rule #End.live          => 6
    rule #End.when          => 7
    rule #End.wait          => 8
    rule #End.debt          => 9
    rule #End.tag[ILK]      => #hashedLocation("Solidity", 10, ILK)
    rule #End.gap[ILK]      => #hashedLocation("Solidity", 11, ILK)
    rule #End.Art[ILK]      => #hashedLocation("Solidity", 12, ILK)
    rule #End.fix[ILK]      => #hashedLocation("Solidity", 13, ILK)
    rule #End.bag[USR]      => #hashedLocation("Solidity", 14, USR)
    rule #End.out[ILK][USR] => #hashedLocation("Solidity", 15, ILK USR)

 // ### Pot
 // -------

    syntax Int ::= "#Pot.wards" "[" Int "]" [macro]
                 | "#Pot.pie" "[" Int "]"   [macro]
                 | "#Pot.Pie"               [macro]
                 | "#Pot.dsr"               [macro]
                 | "#Pot.chi"               [macro]
                 | "#Pot.vat"               [macro]
                 | "#Pot.vow"               [macro]
                 | "#Pot.rho"               [macro]
                 | "#Pot.live"              [macro]
 // -----------------------------------------------
    rule #Pot.wards[A] => #hashedLocation("Solidity", 0, A)
    rule #Pot.pie[USR] => #hashedLocation("Solidity", 1, USR)
    rule #Pot.Pie      => 2
    rule #Pot.dsr      => 3
    rule #Pot.chi      => 4
    rule #Pot.vat      => 5
    rule #Pot.vow      => 6
    rule #Pot.rho      => 7
    rule #Pot.live     => 8

 // ### DSToken
 // -----------

    syntax Int ::= "#DSToken.supply"                         [macro]
                 | "#DSToken.balances" "[" Int "]"           [macro]
                 | "#DSToken.allowance" "[" Int "][" Int "]" [macro]
                 | "#DSToken.authority"                      [macro]
                 | "#DSToken.owner_stopped"                  [macro]
                 | "#DSToken.symbol"                         [macro]
                 | "#DSToken.decimals"                       [macro]
 // ----------------------------------------------------------------
    rule #DSToken.supply          => 0
    rule #DSToken.balances[A]     => #hashedLocation("Solidity", 1, A)
    rule #DSToken.allowance[A][B] => #hashedLocation("Solidity", 2, A B)
    rule #DSToken.authority       => 3
    rule #DSToken.owner_stopped   => 4
    rule #DSToken.symbol          => 5
    rule #DSToken.decimals        => 6

 // ### DSValue
 // -----------

    syntax Int ::= "#DSValue.authority" [macro]
                 | "#DSValue.owner_has" [macro]
                 | "#DSValue.val"       [macro]
 // -------------------------------------------
    rule #DSValue.authority => 0
    rule #DSValue.owner_has => 1
    rule #DSValue.val       => 2

 // ### Spotter
 // -----------

    syntax Int ::= "#Spotter.wards" "[" Int "]"    [macro]
                 | "#Spotter.ilks" "[" Int "].pip" [macro]
                 | "#Spotter.ilks" "[" Int "].mat" [macro]
                 | "#Spotter.vat"                  [macro]
                 | "#Spotter.par"                  [macro]
                 | "#Spotter.live"                 [macro]
 // ------------------------------------------------------
    rule #Spotter.wards[A]      => #hashedLocation("Solidity", 0, A)
    rule #Spotter.ilks[ILK].pip => #hashedLocation("Solidity", 1, ILK) +Int 0
    rule #Spotter.ilks[ILK].mat => #hashedLocation("Solidity", 1, ILK) +Int 1
    rule #Spotter.vat           => 2
    rule #Spotter.par           => 3
    rule #Spotter.live          => 4

endmodule
