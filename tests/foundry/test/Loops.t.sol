// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract LoopsTest is Test {

    uint constant WAD = 10 ** 18;
    uint constant RAY = 10 ** 27;

    function wmul(uint x, uint y) internal pure returns (uint z) {
        z = ((x * y) + (WAD / 2)) / WAD;
    }

    function wdiv(uint x, uint y) internal pure returns (uint z) {
        z = ((x * WAD) + (y / 2)) / y;
    }

    function sumToN(uint256 n) internal pure returns (uint256) {
        uint256 result = 0;
        for (uint256 i = 0; i <= n; i++) {
            result += i;
        }
        return result;
    }

    function sumToNBroken(uint256 n) internal pure returns (uint256) {
        uint256 result = 0;
        // Off by one error in loop condition
        for (uint256 i = 0; i < n; i++) {
            result += i;
        }
        return result;
    }

    function testSumToN(uint256 n) public {
        vm.assume(n <= 100); // We need this to keep the test running time low
        uint256 expected = n * (n + 1) / 2;
        uint256 actual = sumToN(n);
        assertEq(expected, actual);
    }

    function testSumToNBroken(uint256 n) public {
        // This test should fail
        vm.assume(n <= 100); // We need this to keep the test running time low
        uint256 expected = n * (n + 1) / 2;
        uint256 actual = sumToNBroken(n);
        assertEq(expected, actual);
    }

    function sum_N(uint n) public returns (uint) {
        // Amount of gas left at beginning of loop: 9223372036854772642
        // Amount of gas consumed per iteration: 178
        // Number of iterations: n
        // 9223372036854772642 // 178 = 51816696836262767
        vm.assume(n <= 51816696836262767);
        uint s = 0;
        while (0 < n) {
            s = s + n;
            n = n - 1;
        }
        return s;
    }

    function test_sum_10() public returns (uint) {
        return sum_N(10);
    }

    function test_sum_100() public returns (uint) {
        return sum_N(100);
    }

    function test_sum_1000() public returns (uint) {
        return sum_N(1000);
    }
    
    function max(uint256[] memory numbers) internal pure returns (uint256) {
        uint256 result = 0;
        for (uint256 i = 0; i < numbers.length; i++) {
            if (numbers[i] > result) result = numbers[i];
        }
        return result;
    }

    function maxBroken(uint256[] memory numbers) internal pure returns (uint256) {
        uint256 result = 0;
        // Off by one error in loop initialization
        for (uint256 i = 1; i < numbers.length; i++) {
            if (numbers[i] > result) result = numbers[i];
        }
        return result;
    }

    function testMax(uint256[] memory numbers) public {
        uint256 maxium = max(numbers);
        bool isMax = true;
        for (uint256 i = 0; i < numbers.length && isMax; i++) {
            isMax = maxium >= numbers[i];
        }
        assertTrue(isMax);
    }

    function testMaxBroken(uint256[] memory numbers) public {
        // This test should fail
        uint256 maxium = maxBroken(numbers);
        bool isMax = true;
        for (uint256 i = 0; i < numbers.length && isMax; i++) {
            isMax = maxium >= numbers[i];
        }
        assertTrue(isMax);
    }

    function sort(uint256[] memory numbers) internal pure returns(uint256[] memory) {
        if (numbers.length <= 1) return numbers;
        quickSort(numbers, 0, numbers.length - 1);
        return numbers;
    }

    function sortBroken(uint256[] memory numbers) internal pure returns(uint256[] memory) {
        if (numbers.length <= 1) return numbers;
        // Off by one error in second parameter
        quickSort(numbers, 1, numbers.length - 1);
        return numbers;
    }

    function quickSort(uint[] memory numbers, uint left, uint right) internal pure {
        if (left >= right) return;
        uint i = left;
        uint j = right;
        uint pivot = numbers[left + (right - left) / 2];
        while (i <= j) {
            while (numbers[i] < pivot) i++;
            while (pivot < numbers[j] && j > 0) j--;
            if (i <= j) {
                (numbers[i], numbers[j]) = (numbers[j], numbers[i]);
                i++;
                if (j > 0) j--;
            }
        }
        if (left < j)
            quickSort(numbers, left, j);
        if (i < right)
            quickSort(numbers, i, right);
    }

    function testSort(uint256[] memory numbers) public {
        uint256[] memory sorted = sort(numbers);
        bool isSorted = true;
        for (uint256 i = 1; i < sorted.length && isSorted; i++) {
            isSorted = numbers[i - 1] <= numbers[i];
        }
        assertTrue(isSorted);
    }

    function testSortBroken(uint256[] memory numbers) public {
        // This test should fail
        uint256[] memory sorted = sortBroken(numbers);
        bool isSorted = true;
        for (uint256 i = 1; i < sorted.length && isSorted; i++) {
            isSorted = numbers[i - 1] <= numbers[i];
        }
        assertTrue(isSorted);
    }

    function sqrt(uint x) internal pure returns (uint y) {
        if (x == 0) {
            y = 0;
        } else {
            uint z = x;
            while (true) {
                y = z;
                z = (wdiv(x, z) + z) / 2;
                if (y == z) {
                    break;
                }
            }
        }
    }

    function testSqrt(uint x) public {
        uint res = sqrt(x);
        uint sqr = wmul(res, res);
        uint err;
        if (sqr > x) {
            err = sqr - x;
        } else {
            err = sqr - res;
        }
        assertTrue(err < x / 100);
    }

    function isPrimeBroken(uint n) internal pure returns (bool) {
        for (uint i = 2; i < n; i++) {
            if (n % i != 0) {
                return false;
            }
        }
        return true;
    }

    function testIsPrimeBroken(uint n, uint i) public {
        // This test should fail for n < 2
        bool prime = isPrimeBroken(n);
        assertTrue(!prime || n > 1);
        assertTrue(i < 2 || i >= n || !prime || (n % i != 0));
    }

    function isPrime(uint n) internal pure returns (bool) {
        if (n < 2) {
            return false;
        }
        for (uint i = 2; i < n; i++) {
            if (n % i != 0) {
                return false;
            }
        }
        return true;
    }

    function testIsPrime(uint n, uint i) public {
        bool prime = isPrime(n);
        assertTrue(!prime || n > 1);
        assertTrue(i < 2 || i >= n || !prime || (n % i != 0));
    }

    function testIsNotPrime(uint n) public {
        bool prime = isPrime(n);
        if (prime || n < 2) {
            return;
        }
        for (uint i = 2; i < n; i++) {
            if (n % i == 0) {
                return;
            }
        }
        assertTrue(false);
    }

    function isPrimeOpt(uint n) internal pure returns (bool) {
        if (n < 2) {
            return false;
        }
        for (uint i = 2; i <= n / 2; i++) {
            if (n % i != 0) {
                return false;
            }
        }
        return true;
    }

    function testIsPrimeOpt(uint n) public {
        assertEq(isPrime(n), isPrimeOpt(n));
    }

    function nthPrime(uint n) internal pure returns (uint i) {
        uint m;
        while (m < n) {
            i++;
            if (isPrime(i)) {
                m++;
            }
        }
    }

    function testNthPrime(uint n, uint i) public {
        uint nth = nthPrime(n);

        if (n == 0) {
            assertEq(nth, 0);
            return;
        }

        assertTrue(isPrime(nth));

        uint prev = nthPrime(n - 1);
        assertTrue(i <= prev || i >= nth || !isPrime(i));
    }
}
