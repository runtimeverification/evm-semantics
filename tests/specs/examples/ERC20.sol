// THIS IS A BUGGY ERC20
// DO NOT USE FOR ANYTHING

pragma solidity >=0.6.0;

contract ERC20 {

    mapping(address => uint256)                     private _balances;
    mapping(address => mapping(address => uint256)) private _allowances;

    uint256 private _totalSupply;
    uint8 private _decimals;
    string private _name;
    string private _symbol;

    constructor (
        string memory name
      , string memory symbol
      , address initAccount
      , uint256 initSupply
      , uint8 decimals
      ) public {
        _name = name;
        _symbol = symbol;
        _decimals = decimals;
        _mint(initAccount, initSupply);
    }

    function name()        public view returns (string memory) { return _name;        }
    function symbol()      public view returns (string memory) { return _symbol;      }
    function decimals()    public view returns (uint256)       { return _decimals;    }
    function totalSupply() public view returns (uint256)       { return _totalSupply; }

    function balanceOf(address account) external view returns (uint256) {
        return _balances[account];
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        _transfer(msg.sender, to, amount);
        return true;
    }

    function allowance(address owner, address spender) external view returns (uint256) {
        return _allowances[owner][spender];
    }

    function approve(address spender, uint256 amount) external returns (bool) {
        _approve(msg.sender, spender, amount);
        return true;
    }

    function transferFrom(address from, address to, uint256 amount) external returns (bool) {
        _transfer(from, to, amount);

        uint256 currentAllowance = _allowances[from][msg.sender];
        require(currentAllowance >= amount, "ERC20: transfer amount exceeds allowance");
        _approve(from, msg.sender, currentAllowance - amount);

        return true;
    }

    function _transfer(address from, address to, uint256 amount) internal {
        require(from != address(0), "ERC20: transfer from the zero address");
        require(to != address(0), "ERC20: transfer to the zero address");
        uint256 toBalance   = _balances[to];
        uint256 fromBalance = _balances[from];
        require(fromBalance >= amount, "ERC20: transfer amount exceeds balance");
        uint256 fromBalanceUpdated = fromBalance - amount;
        uint256 toBalanceUpdated   = toBalance   + amount;
        _balances[from] = fromBalanceUpdated;
        _balances[to]   = toBalanceUpdated;
    }

    function _approve(address owner, address spender, uint256 amount) internal {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
    }

    function _mint(address account, uint256 amount) internal {
        require(account != address(0), "ERC20: mint to the zero address");
        require(_totalSupply <= _totalSupply + amount);//check overflow on totalSupply
        _totalSupply = _totalSupply + amount;
        _balances[account] = _balances[account] + amount;
    }

    function _burn(address account, uint256 amount) internal {
        require(account != address(0), "ERC20: burn from the zero address");
        require(_balances[account] >= _balances[account] - amount);//check underflow on balances
        _totalSupply = _totalSupply - amount;
        _balances[account] = _balances[account] - amount;
    }
}
