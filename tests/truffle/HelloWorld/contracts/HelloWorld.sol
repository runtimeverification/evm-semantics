pragma solidity ^0.5.8;

contract HelloWorld {
    string private message = "hello world";

    function getMessage() public view returns(string memory) {
        return message;
    }

    function setMessage(string memory newMessage) public {
        message = newMessage;
    }
}
