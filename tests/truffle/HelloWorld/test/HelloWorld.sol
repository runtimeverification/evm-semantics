pragma solidity ^0.5.8;

import "truffle/Assert.sol";
import "truffle/DeployedAddresses.sol";
import "../contracts/HelloWorld.sol";

contract TestHelloWorld {
  function testgetMessage() public {
    HelloWorld hw = HelloWorld(DeployedAddresses.HelloWorld());
    Assert.equal("hello world", hw.getMessage(), "String should match");
  }
}
