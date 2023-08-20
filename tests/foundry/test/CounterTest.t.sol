// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.13;

import "forge-std/Test.sol";
import "../src/KEVMCheats.sol";

contract Counter {
    int120 public number;

    function setNumber(int120 newNumber) public {
        number = newNumber;
    }

    function increment() public {
        number++;
    }
}

contract CounterTest is Test, KEVMCheats {
    Counter public counter;
    
    // function setUp() public {
    //     counter = new Counter();
    //     counter.setNumber(0);
    // }

    function testIncrement() public {
        counter = new Counter();
        counter.setNumber(0);
        counter.increment();
        assertEq(counter.number(), 1);
    }

    function testSetNumber(int120 x) public {
        //setUp();
        counter = new Counter();
        counter.setNumber(0);
        counter.setNumber(x);
        assertEq(counter.number(), x);
    }
}
