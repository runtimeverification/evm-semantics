pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract ERC20 {
    function name() public view returns (string memory) {}
    function symbol() public view returns (string memory) {}
    function decimals() public view returns (uint8) {}
    function totalSupply() public view returns (uint256) {}
    function balanceOf(address account) public view returns (uint256) {}
    function transfer(address to, uint256 amount) public returns (bool) {}
    function allowance(address owner, address spender) public view returns (uint256) {}
    function approve(address spender, uint256 amount) public returns (bool) {}
    function transferFrom(address from, address to, uint256 amount) public returns (bool) {}
    function increaseAllowance(address spender, uint256 addedValue) public returns (bool) {}
    function decreaseAllowance(address spender, uint256 subtractedValue) public returns (bool) {}
}

contract ERC20Test is Test {
    ERC20 erc20;

    function setUp() public {
        erc20 = new ERC20();
    }

    function testCallOther(bytes4 signature, bytes memory args) public {
        vm.assume(signature != bytes4(keccak256(bytes("decimals()"))));
        vm.assume(signature != bytes4(keccak256(bytes("name()"))));
        vm.assume(signature != bytes4(keccak256(bytes("symbol()"))));
        vm.assume(signature != bytes4(keccak256(bytes("totalSupply()"))));
        vm.assume(signature != bytes4(keccak256(bytes("balanceOf(address)"))));
        vm.assume(signature != bytes4(keccak256(bytes("transfer(address,uint256)"))));
        vm.assume(signature != bytes4(keccak256(bytes("transferFrom(address,address,uint256)"))));
        vm.assume(signature != bytes4(keccak256(bytes("allowance(address,address)"))));
        vm.assume(signature != bytes4(keccak256(bytes("approve(address,uint256)"))));
        vm.assume(signature != bytes4(keccak256(bytes("mint(address,uint256)"))));
        vm.assume(signature != bytes4(keccak256(bytes("burn(address,uint256)"))));
        vm.expectRevert();
        address(erc20).call(abi.encodeWithSelector(signature, args));
    }
}

