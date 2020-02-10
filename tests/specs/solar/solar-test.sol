pragma solidity 0.5.10;

contract SolarTest {
    event TestEvent(uint _oldVal, uint _newVal);

    uint private s;

    function add(uint value)
        public
        returns (uint)
    {
        uint sum = s + value;
        s = sum;
        emit TestEvent(s, sum);
        return sum;
    }
}
