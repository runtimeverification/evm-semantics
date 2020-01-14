pragma solidity ^0.5.8;

import "truffle/Assert.sol";
import "truffle/DeployedAddresses.sol";
import "../contracts/HelloWorld.sol";

contract TestHelloWorld {
  string expected = "hello world";

  function testgetMessage() public {
    HelloWorld hw = HelloWorld(DeployedAddresses.HelloWorld());
    Assert.equal(hw.getMessage(), expected, "String should match");
  }
}
