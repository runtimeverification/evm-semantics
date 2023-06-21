// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

contract UintTypeTest {

    /* Tests for uint256 */
    function test_uint256(uint256 x) public pure {
        assert(x == x);
        assert(type(uint256).max >= x);
    }

    function test_uint256_fail(uint256 x) public pure {
        assert(type(uint256).max > x);
    }

    function testFail_uint256(uint256 x) public pure {
        assert(type(uint256).max > x);
    }


    /* Tests for uint248 */
    function test_uint248(uint248 x) public pure {
        assert(x == x);
        assert(type(uint248).max >= x);
    }

    function test_uint248_fail(uint248 x) public pure {
        assert(type(uint248).max > x);
    }

    function testFail_uint248(uint248 x) public pure {
        assert(type(uint248).max > x);
    }


    /* Tests for uint240 */
    function test_uint240(uint240 x) public pure {
        assert(x == x);
        assert(type(uint240).max >= x);
    }

    function test_uint240_fail(uint240 x) public pure {
        assert(type(uint240).max > x);
    }

    function testFail_uint240(uint240 x) public pure {
        assert(type(uint240).max > x);
    }


    /* Tests for uint232 */
    function test_uint232(uint232 x) public pure {
        assert(x == x);
        assert(type(uint232).max >= x);
    }

    function test_uint232_fail(uint232 x) public pure {
        assert(type(uint232).max > x);
    }

    function testFail_uint232(uint232 x) public pure {
        assert(type(uint232).max > x);
    }


    /* Tests for uint224 */
    function test_uint224(uint224 x) public pure {
        assert(x == x);
        assert(type(uint224).max >= x);
    }

    function test_uint224_fail(uint224 x) public pure {
        assert(type(uint224).max > x);
    }

    function testFail_uint224(uint224 x) public pure {
        assert(type(uint224).max > x);
    }


    /* Tests for uint216 */
    function test_uint216(uint216 x) public pure {
        assert(x == x);
        assert(type(uint216).max >= x);
    }

    function test_uint216_fail(uint216 x) public pure {
        assert(type(uint216).max > x);
    }

    function testFail_uint216(uint216 x) public pure {
        assert(type(uint216).max > x);
    }


    /* Tests for uint208 */
    function test_uint208(uint208 x) public pure {
        assert(x == x);
        assert(type(uint208).max >= x);
    }

    function test_uint208_fail(uint208 x) public pure {
        assert(type(uint208).max > x);
    }

    function testFail_uint208(uint208 x) public pure {
        assert(type(uint208).max > x);
    }


    /* Tests for uint200 */
    function test_uint200(uint200 x) public pure {
        assert(x == x);
        assert(type(uint200).max >= x);
    }

    function test_uint200_fail(uint200 x) public pure {
        assert(type(uint200).max > x);
    }

    function testFail_uint200(uint200 x) public pure {
        assert(type(uint200).max > x);
    }


    /* Tests for uint192 */
    function test_uint192(uint192 x) public pure {
        assert(x == x);
        assert(type(uint192).max >= x);
    }

    function test_uint192_fail(uint192 x) public pure {
        assert(type(uint192).max > x);
    }

    function testFail_uint192(uint192 x) public pure {
        assert(type(uint192).max > x);
    }


    /* Tests for uint184 */
    function test_uint184(uint184 x) public pure {
        assert(x == x);
        assert(type(uint184).max >= x);
    }

    function test_uint184_fail(uint184 x) public pure {
        assert(type(uint184).max > x);
    }

    function testFail_uint184(uint184 x) public pure {
        assert(type(uint184).max > x);
    }


    /* Tests for uint176 */
    function test_uint176(uint176 x) public pure {
        assert(x == x);
        assert(type(uint176).max >= x);
    }

    function test_uint176_fail(uint176 x) public pure {
        assert(type(uint176).max > x);
    }

    function testFail_uint176(uint176 x) public pure {
        assert(type(uint176).max > x);
    }


    /* Tests for uint168 */
    function test_uint168(uint168 x) public pure {
        assert(x == x);
        assert(type(uint168).max >= x);
    }

    function test_uint168_fail(uint168 x) public pure {
        assert(type(uint168).max > x);
    }

    function testFail_uint168(uint168 x) public pure {
        assert(type(uint168).max > x);
    }


    /* Tests for uint160 */
    function test_uint160(uint160 x) public pure {
        assert(x == x);
        assert(type(uint160).max >= x);
    }

    function test_uint160_fail(uint160 x) public pure {
        assert(type(uint160).max > x);
    }

    function testFail_uint160(uint160 x) public pure {
        assert(type(uint160).max > x);
    }


    /* Tests for uint152 */
    function test_uint152(uint152 x) public pure {
        assert(x == x);
        assert(type(uint152).max >= x);
    }

    function test_uint152_fail(uint152 x) public pure {
        assert(type(uint152).max > x);
    }

    function testFail_uint152(uint152 x) public pure {
        assert(type(uint152).max > x);
    }


    /* Tests for uint144 */
    function test_uint144(uint144 x) public pure {
        assert(x == x);
        assert(type(uint144).max >= x);
    }

    function test_uint144_fail(uint144 x) public pure {
        assert(type(uint144).max > x);
    }

    function testFail_uint144(uint144 x) public pure {
        assert(type(uint144).max > x);
    }


    /* Tests for uint136 */
    function test_uint136(uint136 x) public pure {
        assert(x == x);
        assert(type(uint136).max >= x);
    }

    function test_uint136_fail(uint136 x) public pure {
        assert(type(uint136).max > x);
    }

    function testFail_uint136(uint136 x) public pure {
        assert(type(uint136).max > x);
    }


    /* Tests for uint128 */
    function test_uint128(uint128 x) public pure {
        assert(x == x);
        assert(type(uint128).max >= x);
    }

    function test_uint128_fail(uint128 x) public pure {
        assert(type(uint128).max > x);
    }

    function testFail_uint128(uint128 x) public pure {
        assert(type(uint128).max > x);
    }


    /* Tests for uint120 */
    function test_uint120(uint120 x) public pure {
        assert(x == x);
        assert(type(uint120).max >= x);
    }

    function test_uint120_fail(uint120 x) public pure {
        assert(type(uint120).max > x);
    }

    function testFail_uint120(uint120 x) public pure {
        assert(type(uint120).max > x);
    }


    /* Tests for uint112 */
    function test_uint112(uint112 x) public pure {
        assert(x == x);
        assert(type(uint112).max >= x);
    }

    function test_uint112_fail(uint112 x) public pure {
        assert(type(uint112).max > x);
    }

    function testFail_uint112(uint112 x) public pure {
        assert(type(uint112).max > x);
    }


    /* Tests for uint104 */
    function test_uint104(uint104 x) public pure {
        assert(x == x);
        assert(type(uint104).max >= x);
    }

    function test_uint104_fail(uint104 x) public pure {
        assert(type(uint104).max > x);
    }

    function testFail_uint104(uint104 x) public pure {
        assert(type(uint104).max > x);
    }


    /* Tests for uint96 */
    function test_uint96(uint96 x) public pure {
        assert(x == x);
        assert(type(uint96).max >= x);
    }

    function test_uint96_fail(uint96 x) public pure {
        assert(type(uint96).max > x);
    }

    function testFail_uint96(uint96 x) public pure {
        assert(type(uint96).max > x);
    }


    /* Tests for uint88 */
    function test_uint88(uint88 x) public pure {
        assert(x == x);
        assert(type(uint88).max >= x);
    }

    function test_uint88_fail(uint88 x) public pure {
        assert(type(uint88).max > x);
    }

    function testFail_uint88(uint88 x) public pure {
        assert(type(uint88).max > x);
    }


    /* Tests for uint80 */
    function test_uint80(uint80 x) public pure {
        assert(x == x);
        assert(type(uint80).max >= x);
    }

    function test_uint80_fail(uint80 x) public pure {
        assert(type(uint80).max > x);
    }

    function testFail_uint80(uint80 x) public pure {
        assert(type(uint80).max > x);
    }


    /* Tests for uint72 */
    function test_uint72(uint72 x) public pure {
        assert(x == x);
        assert(type(uint72).max >= x);
    }

    function test_uint72_fail(uint72 x) public pure {
        assert(type(uint72).max > x);
    }

    function testFail_uint72(uint72 x) public pure {
        assert(type(uint72).max > x);
    }


    /* Tests for uint64 */
    function test_uint64(uint64 x) public pure {
        assert(x == x);
        assert(type(uint64).max >= x);
    }

    function test_uint64_fail(uint64 x) public pure {
        assert(type(uint64).max > x);
    }

    function testFail_uint64(uint64 x) public pure {
        assert(type(uint64).max > x);
    }


    /* Tests for uint56 */
    function test_uint56(uint56 x) public pure {
        assert(x == x);
        assert(type(uint56).max >= x);
    }

    function test_uint56_fail(uint56 x) public pure {
        assert(type(uint56).max > x);
    }

    function testFail_uint56(uint56 x) public pure {
        assert(type(uint56).max > x);
    }


    /* Tests for uint48 */
    function test_uint48(uint48 x) public pure {
        assert(x == x);
        assert(type(uint48).max >= x);
    }

    function test_uint48_fail(uint48 x) public pure {
        assert(type(uint48).max > x);
    }

    function testFail_uint48(uint48 x) public pure {
        assert(type(uint48).max > x);
    }


    /* Tests for uint40 */
    function test_uint40(uint40 x) public pure {
        assert(x == x);
        assert(type(uint40).max >= x);
    }

    function test_uint40_fail(uint40 x) public pure {
        assert(type(uint40).max > x);
    }

    function testFail_uint40(uint40 x) public pure {
        assert(type(uint40).max > x);
    }


    /* Tests for uint32 */
    function test_uint32(uint32 x) public pure {
        assert(x == x);
        assert(type(uint32).max >= x);
    }

    function test_uint32_fail(uint32 x) public pure {
        assert(type(uint32).max > x);
    }

    function testFail_uint32(uint32 x) public pure {
        assert(type(uint32).max > x);
    }


    /* Tests for uint24 */
    function test_uint24(uint24 x) public pure {
        assert(x == x);
        assert(type(uint24).max >= x);
    }

    function test_uint24_fail(uint24 x) public pure {
        assert(type(uint24).max > x);
    }

    function testFail_uint24(uint24 x) public pure {
        assert(type(uint24).max > x);
    }


    /* Tests for uint16 */
    function test_uint16(uint16 x) public pure {
        assert(x == x);
        assert(type(uint16).max >= x);
    }

    function test_uint16_fail(uint16 x) public pure {
        assert(type(uint16).max > x);
    }

    function testFail_uint16(uint16 x) public pure {
        assert(type(uint16).max > x);
    }


    /* Tests for uint8 */
    function test_uint8(uint8 x) public pure {
        assert(x == x);
        assert(type(uint8).max >= x);
    }

    function test_uint8_fail(uint8 x) public pure {
        assert(type(uint8).max > x);
    }

    function testFail_uint8(uint8 x) public pure {
        assert(type(uint8).max > x);
    }

}

contract BytesTypeTest {

    /* Tests for bytes32 */
    function test_bytes32(bytes32 x) public pure {
        assert(x == x);
        assert(type(uint256).max >= uint256(x));
    }

    function test_bytes32_fail(bytes32 x) public pure {
        assert(type(uint256).max > uint256(x));
    }

    function testFail_bytes32(bytes32 x) public pure {
        assert(type(uint256).max > uint256(x));
    }


    /* Tests for bytes4 */
    function test_bytes4(bytes4 x) public pure {
        assert(x == x);
        assert(type(uint32).max >= uint32(x));
    }

    function test_bytes4_fail(bytes4 x) public pure {
        assert(type(uint32).max > uint32(x));
    }

    function testFail_bytes4(bytes4 x) public pure {
        assert(type(uint32).max > uint32(x));
    }
}
