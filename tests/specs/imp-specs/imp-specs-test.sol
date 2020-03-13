pragma solidity 0.5.0;

contract ImpSpecsTest {
    event TestEvent(uint _oldVal, uint _newVal);

    uint private s;

    function add(uint value)
        public
        returns (uint)
    {
        uint oldS = s;
        uint sum = s + value;
        s = sum;
        emit TestEvent(oldS, sum);
        return sum;
    }
}
