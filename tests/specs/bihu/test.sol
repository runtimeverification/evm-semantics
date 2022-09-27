// Decompiled by library.dedaub.com
// 2022.09.13 14:18 UTC

// Data structures and variables inferred from the use of storage instructions
// ok
uint256 _collectedTokens; // STORAGE[0x0]
uint256 _balance; // STORAGE[0x1]


function balance() public nonPayable {
    return _balance;
}

function collectToken(uint256 NOW, uint256 START) public nonPayable {
    require(NOW > START); // ok
    v0 = v1 = _collectedTokens + _balance;
    assert(v1 >= _collectedTokens); // ok (both are non negative)
    v2 = _SafeSubAndMod(START, NOW); // safe NOW - START and modulo 31536000
    v3 = v4 = 0;
    while (v3 < v2) {
      // yearly percentage return
        v0 = _SafeMul(90, v0) / 100;
        v3 += 1;
    }

    // v3 == v2
    // v0 == (COLLECTED + BAL) * 90^(NOW - START) / 100^(NOW - START) <= COLLECTED + BAL

    v6 = _SafeMul(10, v0);

    // v6 = 9 * (COLLECTED + BAL) * (9/10)^(NOW-START-1)

    v7 = v8 = v6 / 100 == 0;
    if (v6 / 100 != 0) {
        assert(v6 / 100); // ok
        v7 = v6 / 100 * ((NOW - START) %Int 31536000) / (v6 / 100) == (NOW - START) %Int 31536000; // should I add to condition?
    }
    assert(v7); // ok

    v10 = (((v6 / 100) * ((NOW - START) %Int 31536000)) / 31536000) + (v1 - v0) - _collectedTokens;
    // fails here
    assert(v10 <= v6 / 100 * ((NOW - START) %Int 31536000) / 31536000 + (v1 - v0)); // collectedTokens is nonnegative

    // COLLECTED <= (v6 / 100) * ((NOW - START) %Int 31536000) / 31536000 + (COLLECTED + BAL - v0)
    // 0 <= (9 * (COLLECTED + BAL) * (9/10)^(NOW-START-1) / 100) * ((NOW - START) %Int 31536000) / 31536000 + (BAL - v0)

    if (v10 > _balance) {
        v10 = v11 = _balance;
    }

    assert(_collectedTokens + v10 >= _collectedTokens); // check
    _collectedTokens = _collectedTokens + v10;
    assert(_balance - v10 <= _balance); // check v10 can be negative
    _balance = _balance - v10;

    return 1;
}

function _SafeSubAndMod(uint256 START, uint256 NOW) private {
    if (NOW < START) {
        v0 = v1 = 0;
    } else {
        v2 = NOW - START;
        assert(v2 <= NOW); // ok
        assert(31536000); // ok
        v0 = v3 = v2 / 31536000;
    }
    return v0;
}

function _SafeMul(uint256 varg0, uint256 varg1) private {
    v0 = varg1 * varg0;
    v1 = v2 = varg1 == 0;
    if (varg1 != 0) {
        assert(varg1); // ok
        v1 = v0 / varg1 == varg0;
    }
    assert(v1); // ok
    return v0;
}

function () public payable {
    revert();
}

function yearlyRewardPercentage() public nonPayable {
    return 10;
}

function notusedanywhere(uint256 varg0, uint256 varg1) public nonPayable {
    v0 = _SafeSubAndMod(varg1, varg0);
    return v0;
}

function collectedTokens() public nonPayable {
    return _collectedTokens;
}

// Note: The function selector is not present in the original solidity code.
// However, we display it for the sake of completeness.

function __function_selector__(bytes4 function_selector) public payable {
    MEM[64] = 96;
    if (msg.data.length >= 4) {
        if (0xe4aed3f == uint32(function_selector >> 224)) {
            yearlyRewardPercentage();
        } else if (notusedanywhere == uint32(function_selector >> 224)) {
            notusedanywhere();
        } else if (0x787e9137 == uint32(function_selector >> 224)) {
            collectedTokens();
        } else if (0xb69ef8a8 == uint32(function_selector >> 224)) {
            balance();
        } else if (collectToken == uint32(function_selector >> 224)) {
            collectToken();
        }
    }
    ();
}
