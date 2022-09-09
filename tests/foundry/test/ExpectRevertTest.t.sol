// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract Guess {
    uint256 value;

    constructor (uint256 _value){
        value = _value;
    }

    function guessTheValue(uint256 _value) public view returns (bool) {
        require(_value == value);
        return true;
    }

}
contract CheckRevert {
    bool a;
    Guess guess;

    constructor (bool _a, uint256 _b){
        a = _a;
        guess = new Guess(_b);
    }

    function revertIfNotEqual(bool value) public view returns(bool){
        require(value == a, "error message");
        return true;
    }

    function tryToGuess(uint256 _value) public view returns (bool){
        return guess.guessTheValue(_value);
    }
}
contract ExpectRevertTest is Test {

    function test_expectRevert_true() public {
        CheckRevert checkRevert = new CheckRevert(false, 0);
        vm.expectRevert(bytes("error message"));
        checkRevert.revertIfNotEqual(true);
    }

    function testFail_expectRevert_false() public {
        CheckRevert checkRevert = new CheckRevert(false, 0);
        vm.expectRevert(bytes("error"));
        checkRevert.revertIfNotEqual(true);
    }

    function test_expectRevert_true2() public {
        CheckRevert checkRevert = new CheckRevert(false, 1);
        vm.expectRevert();
        checkRevert.tryToGuess(2);
    }

    function testFail_expectRevert_false2() public {
        CheckRevert checkRevert = new CheckRevert(false, 0);
        vm.expectRevert(bytes("error"));
        checkRevert.revertIfNotEqual(false);
    }

}
