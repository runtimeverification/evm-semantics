// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract DifferentToken {
    uint256 value;

    constructor (uint256 _value){
        value = _value;
    }

    function guessTheValue(uint256 _value) public view returns (bool) {
        require(_value == value);
        return true;
    }

}
contract Token {
    bool a;
    DifferentToken token;

    constructor (bool _a, uint256 _b){
        a = _a;
        token = new DifferentToken(_b);
    }

    function revertIfNotEqual(bool value) public view returns(bool){
        require(value == a, "error message");
        return true;
    }

    function tryToGuess(uint256 _value) public view returns (bool){
        return token.guessTheValue(_value);
    }
}
contract ExpectRevertTest is Test {

    function test_expectRevert_true() public {
        Token token = new Token(false, 0);
        vm.expectRevert(bytes("error message"));
        token.revertIfNotEqual(true);
    }

    function test_expectRevert_false() public {
        Token token = new Token(false, 0);
        vm.expectRevert(bytes("error"));
        token.revertIfNotEqual(true);
    }

    function test_expectRevert_true2() public {
        Token token = new Token(false, 1);
        vm.expectRevert();
        token.tryToGuess(2);
    }

    function test_expectRevert_false2() public {
        Token token = new Token(false, 0);
        vm.expectRevert(bytes("error"));
        token.revertIfNotEqual(false);
    }

}