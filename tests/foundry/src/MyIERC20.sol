// SPDX-License-Identifier: GPL-3.0-or-later
pragma solidity =0.8.13;

interface MyIERC20 {
	function totalSupply() external view returns (uint256);

	function transfer(address recipient, uint256 amount) external returns (bool);

	function decimals() external view returns (uint8);

	function symbol() external view returns (string memory);

	function balanceOf(address) external view returns (uint256);

	function transferFrom(
		address sender,
		address recipient,
		uint256 amount
	) external returns (bool);

	function approve(address spender, uint256 value) external returns (bool);
}