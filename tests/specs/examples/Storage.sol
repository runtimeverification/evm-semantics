// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

contract Storage {
    bool public myBool;

    uint8 public myUint8;
    uint16 public myUint16;
    uint24 public myUint24;
    uint32 public myUint32;
    uint40 public myUint40;
    uint48 public myUint48;
    uint56 public myUint56;
    uint64 public myUint64;
    uint72 public myUint72;
    uint80 public myUint80;
    uint88 public myUint88;
    uint96 public myUint96;
    uint104 public myUint104;
    uint112 public myUint112;
    uint120 public myUint120;
    uint128 public myUint128;
    uint136 public myUint136;
    uint144 public myUint144;
    uint152 public myUint152;
    uint160 public myUint160;
    uint168 public myUint168;
    uint176 public myUint176;
    uint184 public myUint184;
    uint192 public myUint192;
    uint200 public myUint200;
    uint208 public myUint208;
    uint216 public myUint216;
    uint224 public myUint224;
    uint232 public myUint232;
    uint240 public myUint240;
    uint248 public myUint248;
    uint256 public myUint256;

    int8 public myInt8;
    int16 public myInt16;
    int24 public myInt24;
    int32 public myInt32;
    int40 public myInt40;
    int48 public myInt48;
    int56 public myInt56;
    int64 public myInt64;
    int72 public myInt72;
    int80 public myInt80;
    int88 public myInt88;
    int96 public myInt96;
    int104 public myInt104;
    int112 public myInt112;
    int120 public myInt120;
    int128 public myInt128;
    int136 public myInt136;
    int144 public myInt144;
    int152 public myInt152;
    int160 public myInt160;
    int168 public myInt168;
    int176 public myInt176;
    int184 public myInt184;
    int192 public myInt192;
    int200 public myInt200;
    int208 public myInt208;
    int216 public myInt216;
    int224 public myInt224;
    int232 public myInt232;
    int240 public myInt240;
    int248 public myInt248;
    int256 public myInt256;

    string public myString;
    bytes public myBytes;

    uint128[] myUint128s;
    uint64[5] myUint64s;

    struct Foo {
        uint128 myUint128;
        uint8[] myUint8Array;
    }

    Foo myFoo;
    Foo[] myFoos;

    constructor () {
        myBool = true;
        myUint128 = 100;
        myUint256 = 200;
        myString = "foo";
    }

    function setMyBool(bool newBool) public {
        myBool = newBool;
    }

}
