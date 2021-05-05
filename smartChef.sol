// File: @pancakeswap/pancake-swap-lib/contracts/math/SafeMath.sol

// SPDX-License-Identifier: MIT

pragma solidity >=0.4.0;

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, 'SafeMath: addition overflow');

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, 'SafeMath: subtraction overflow');
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, 'SafeMath: multiplication overflow');

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, 'SafeMath: division by zero');
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, 'SafeMath: modulo by zero');
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }

    function min(uint256 x, uint256 y) internal pure returns (uint256 z) {
        z = x < y ? x : y;
    }

    // babylonian method (https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Babylonian_method)
    function sqrt(uint256 y) internal pure returns (uint256 z) {
        if (y > 3) {
            z = y;
            uint256 x = y / 2 + 1;
            while (x < z) {
                z = x;
                x = (y / x + x) / 2;
            }
        } else if (y != 0) {
            z = 1;
        }
    }
}

// File: @pancakeswap/pancake-swap-lib/contracts/token/BEP20/IBEP20.sol

// SPDX-License-Identifier: GPL-3.0-or-later

pragma solidity >=0.4.0;

interface IBEP20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the token decimals.
     */
    function decimals() external view returns (uint8);

    /**
     * @dev Returns the token symbol.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the token name.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the bep token owner.
     */
    function getOwner() external view returns (address);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address _owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

// File: @pancakeswap/pancake-swap-lib/contracts/utils/Address.sol

// SPDX-License-Identifier: MIT

pragma solidity ^0.6.2;

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // According to EIP-1052, 0x0 is the value returned for not-yet created accounts
        // and 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 is returned
        // for accounts without code, i.e. `keccak256('')`
        bytes32 codehash;
        bytes32 accountHash = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470;
        // solhint-disable-next-line no-inline-assembly
        assembly {
            codehash := extcodehash(account)
        }
        return (codehash != accountHash && codehash != 0x0);
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, 'Address: insufficient balance');

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{value: amount}('');
        require(success, 'Address: unable to send value, recipient may have reverted');
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCall(target, data, 'Address: low-level call failed');
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return _functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, 'Address: low-level call with value failed');
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(address(this).balance >= value, 'Address: insufficient balance for call');
        return _functionCallWithValue(target, data, value, errorMessage);
    }

    function _functionCallWithValue(
        address target,
        bytes memory data,
        uint256 weiValue,
        string memory errorMessage
    ) private returns (bytes memory) {
        require(isContract(target), 'Address: call to non-contract');

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{value: weiValue}(data);
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

// File: @pancakeswap/pancake-swap-lib/contracts/token/BEP20/SafeBEP20.sol

// SPDX-License-Identifier: MIT

pragma solidity ^0.6.0;




/**
 * @title SafeBEP20
 * @dev Wrappers around BEP20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeBEP20 for IBEP20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeBEP20 {
    using SafeMath for uint256;
    using Address for address;

    function safeTransfer(
        IBEP20 token,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(
        IBEP20 token,
        address from,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IBEP20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(
        IBEP20 token,
        address spender,
        uint256 value
    ) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            'SafeBEP20: approve from non-zero to non-zero allowance'
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(
        IBEP20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(value);
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(
        IBEP20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(
            value,
            'SafeBEP20: decreased allowance below zero'
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IBEP20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, 'SafeBEP20: low-level call failed');
        if (returndata.length > 0) {
            // Return data is optional
            // solhint-disable-next-line max-line-length
            require(abi.decode(returndata, (bool)), 'SafeBEP20: BEP20 operation did not succeed');
        }
    }
}

// File: @pancakeswap/pancake-swap-lib/contracts/GSN/Context.sol

// SPDX-License-Identifier: GPL-3.0-or-later

pragma solidity >=0.4.0;

/*
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with GSN meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
contract Context {
    // Empty internal constructor, to prevent people from mistakenly deploying
    // an instance of this contract, which should be used via inheritance.
    constructor() internal {}

    function _msgSender() internal view returns (address payable) {
        return msg.sender;
    }

    function _msgData() internal view returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

// File: @pancakeswap/pancake-swap-lib/contracts/access/Ownable.sol

// SPDX-License-Identifier: GPL-3.0-or-later

pragma solidity >=0.4.0;


/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() internal {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(_owner == _msgSender(), 'Ownable: caller is not the owner');
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public onlyOwner {
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     */
    function _transferOwnership(address newOwner) internal {
        require(newOwner != address(0), 'Ownable: new owner is the zero address');
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}

// File: contracts/smartChef.sol

// SPDX-License-Identifier: MIT

pragma solidity 0.6.12;





interface IPhoenixSwapToken is IBEP20 {
    function mint(address _to, uint256 _amount) external;
}


contract SmartChef is Ownable {
    using SafeMath for uint256;
    using SafeBEP20 for IBEP20;

    // Info of each user.
    struct UserInfo {
        uint256 amount;     // How many LP tokens the user has provided.
        uint256 rewardDebt; // Reward debt. See explanation below.
        uint256 rewardDebtAtBlock; // the last block user stake
    }

    // Info of each pool.
    struct PoolInfo {
        IBEP20 stakeToken;           // Address of LP token contract.
        IBEP20 rewardToken;       // Address of reward token contract.  
        uint256 allocPoint;       // How many allocation points assigned to this pool. Rewards to distribute per block.
        uint256 lastRewardBlock;  // Last block number that Rewards distribution occurs.
        uint256 accRewardTokenPerShare; // Accumulated Rewards per share, times 1e12. See below.
        uint16 depositFeeBP;        // Deposit fee in basis points
    }

    // Allocation Info of pool based on rewardToken
    struct AllocInfo {
        IBEP20 rewardToken;
        uint256 rewardPerBlock;
        uint256 totalAllocPoint;
    }

    IPhoenixSwapToken public pnixs;

    // // The stake token
    // IBEP20 public stakeToken;
    // // The reward token
    // IBEP20 public rewardToken;

    // Deposit Fee address
    address public feeAddress;

    // Withdraw Fee address
    address public withdrawFeeAddress;

    // Withdraw Fee
    uint16 public withdrawFee = 5;

    address public devaddr;

    uint256 public stakeAmountLv1 = 100*10**18;    // Minimum stake PNIXS token condition level1 for referral program.
    uint256 public stakeAmountLv2 = 1000*10**18;    // Minimum stake PNIXS token condition level2 for referral program.

    mapping(address => mapping (address => uint256)) public referralAmountLv1;
    mapping(address => mapping (address => uint256)) public referralAmountLv2;

    uint16 public percentForReferLv1 = 5; // Percent reward level1 referral program.
    uint16 public percentForReferLv2 = 3; // Percent reward level2 referral program.
    
    // // Reward tokens created per block.
    // uint256 public rewardPerBlock;

    // Keep track of number of tokens staked in case the contract earns reflect fees
    // uint256 public totalStaked = 0;

    mapping(address => address) public userRef;

    // Info of each pool.
    PoolInfo[] public poolInfo;
    // Allocation Info
    AllocInfo[] private allocInfo;
    // Info of each user that stakes LP tokens.
    mapping (uint256 => mapping (address => UserInfo)) public userInfo;
    // // Total allocation points. Must be the sum of all allocation points in all pools.
    // uint256 private totalAllocPoint = 0;
    // The block number when Reward mining starts.
    uint256 public startBlock;
	// // The block number when mining ends.
    // uint256 public bonusEndBlock;

    uint256 public constant BONUS_MULTIPLIER = 1;

    event Deposit(address indexed user, uint256 indexed pid, uint256 amount);
    event DepositRewards(uint256 amount);
    event Withdraw(address indexed user, uint256 indexed pid, uint256 amount);
    event EmergencyWithdraw(address indexed user, uint256 indexed pid, uint256 amount);
    event EmergencyRewardWithdraw(address indexed user, uint256 amount);
    event SkimStakeTokenFees(address indexed user, uint256 amount);

    constructor(
        IPhoenixSwapToken _pnixs,
        uint256 _startBlock,
        address _feeAddress,
        address _withdrawfeeAddress,
        address _devaddr
    ) public {
        pnixs = _pnixs;
        devaddr = _devaddr;
        feeAddress = _feeAddress;
        startBlock = _startBlock;
        withdrawFeeAddress = _withdrawfeeAddress;
    }

    function poolLength() external view returns (uint256) {
        return poolInfo.length;
    }

    // Add a new lp to the pool. Can only be called by the owner.
    // XXX DO NOT add the same LP token more than once. Rewards will be messed up if you do.
    function add(
        uint256 _allocPoint, 
        IBEP20 _stakeToken,
        IBEP20 _rewardToken,
        uint256 _rewardPerBlock,
        uint16 _depositFeeBP,
        bool _withUpdate
    ) public onlyOwner {
        require(_depositFeeBP <= 10000, "add: invalid deposit fee basis points");
        uint256 length = poolInfo.length;
        for (uint256 pid = 0; pid < length; ++pid) {
            if (poolInfo[pid].stakeToken == _stakeToken)
            {
                return;
            }
        }
        
        if (_withUpdate) {
            massUpdatePools();
        }
        uint256 lastRewardBlock = block.number > startBlock ? block.number : startBlock;
        // totalAllocPoint = totalAllocPoint.add(_allocPoint);
        uint256 aLength = allocInfo.length;
        uint256 aid;
        for (aid = 0; aid < aLength; ++aid) {
            if (allocInfo[aid].rewardToken == _rewardToken) {
                allocInfo[aid].totalAllocPoint.add(_allocPoint);
                break;
            }
        }
        if (aid == aLength || aid > aLength) {
            allocInfo.push(AllocInfo({
                rewardToken: _rewardToken,
                rewardPerBlock: _rewardPerBlock,
                totalAllocPoint: _allocPoint
            }));
        }

        poolInfo.push(PoolInfo({
            stakeToken: _stakeToken,
            rewardToken: _rewardToken,
            allocPoint: _allocPoint,
            lastRewardBlock: lastRewardBlock,
            accRewardTokenPerShare: 0,
            depositFeeBP: _depositFeeBP
        }));
    }

    // Update the given pool's PNIXS allocation point and deposit fee. Can only be called by the owner.
    function set(
        uint256 _pid,
        IBEP20 _stakeToken,
        IBEP20 _rewardToken,
        uint256 _allocPoint,
        uint16 _depositFeeBP,
        bool _withUpdate
    ) public onlyOwner {
        require(_depositFeeBP <= 10000, "set: invalid deposit fee basis points");
       
        
        if (_withUpdate) {
            massUpdatePools();
        }

        IBEP20 prevRewardToken = poolInfo[_pid].rewardToken;
        uint256 aLength = allocInfo.length;
        uint256 aid;
        for (aid = 0; aid < aLength; ++aid) {
            if (allocInfo[aid].rewardToken == prevRewardToken) {
                allocInfo[aid].totalAllocPoint.sub(_allocPoint);
                break;
            }
        }

        for (aid = 0; aid < aLength; ++aid) {
            if (allocInfo[aid].rewardToken == _rewardToken) {
                allocInfo[aid].totalAllocPoint.add(_allocPoint);
                break;
            }
        }
        if (aid == aLength || aid > aLength) {
            allocInfo.push(AllocInfo({
                rewardToken: _rewardToken,
                rewardPerBlock: 0,
                totalAllocPoint: _allocPoint
            }));
        }
        
        poolInfo[_pid].allocPoint = _allocPoint;
        poolInfo[_pid].depositFeeBP = _depositFeeBP;
        poolInfo[_pid].stakeToken = _stakeToken;
    }

    // Return reward multiplier over the given _from to _to block.
    function getMultiplier(uint256 _from, uint256 _to) public pure returns (uint256) {
        return _to.sub(_from).mul(BONUS_MULTIPLIER);
    }

    // View function to see pending Reward on frontend.
    function pendingReward(uint256 _pid, address _user) external view returns (uint256) {
        PoolInfo storage pool = poolInfo[_pid];
        UserInfo storage user = userInfo[_pid][_user];
        uint256 accRewardTokenPerShare = pool.accRewardTokenPerShare;
        uint256 totalStaked = pool.stakeToken.balanceOf(address(this));
        if (block.number > pool.lastRewardBlock && totalStaked != 0) {
            uint256 multiplier = getMultiplier(pool.lastRewardBlock, block.number);
            uint256 totalAllocPoint = _getTotalAllocPoint(_pid);
            uint256 rewardPerBlock = _getRewardPerBlock(_pid);
            uint256 tokenReward = multiplier.mul(rewardPerBlock).mul(pool.allocPoint).div(totalAllocPoint);
            accRewardTokenPerShare = accRewardTokenPerShare.add(tokenReward.mul(1e12).div(totalStaked));
        }
        return user.amount.mul(accRewardTokenPerShare).div(1e12).sub(user.rewardDebt);
    }

    // get total allocation point of specific reward token
    function _getTotalAllocPoint(uint256 _pid) internal view returns (uint256) {
        IBEP20 rewardToken = poolInfo[_pid].rewardToken;
        uint256 aLength = allocInfo.length;
        for (uint256 aid = 0; aid < aLength; ++aid) {
            if (allocInfo[aid].rewardToken == rewardToken) {
                return allocInfo[aid].totalAllocPoint;
            }
        }
    }

    function _getRewardPerBlock(uint256 _pid) internal view returns (uint256) {
        IBEP20 rewardToken = poolInfo[_pid].rewardToken;
        uint256 aLength = allocInfo.length;
        for (uint256 aid = 0; aid < aLength; ++aid) {
            if (allocInfo[aid].rewardToken == rewardToken) {
                return allocInfo[aid].rewardPerBlock;
            }
        }
    }

    // Update reward variables for all pools. Be careful of gas spending!
    function massUpdatePools() public {
        uint256 length = poolInfo.length;
        for (uint256 pid = 0; pid < length; ++pid) {
            updatePool(pid);
        }
    }

    // Update reward variables of the given pool to be up-to-date.
    function updatePool(uint256 _pid) public {
        PoolInfo storage pool = poolInfo[_pid];
        if (block.number <= pool.lastRewardBlock) {
            return;
        }
        uint256 totalStaked = pool.stakeToken.balanceOf(address(this));
        if (totalStaked == 0 || pool.allocPoint == 0) {
            pool.lastRewardBlock = block.number;
            return;
        }
        uint256 multiplier = getMultiplier(pool.lastRewardBlock, block.number);
        uint256 totalAllocPoint = _getTotalAllocPoint(_pid);
        uint256 rewardPerBlock = _getRewardPerBlock(_pid);
        uint256 tokenReward = multiplier.mul(rewardPerBlock).mul(pool.allocPoint).div(totalAllocPoint);
        // pnixs.mint needed?
        safeTransferReward(devaddr, tokenReward.div(10));
        pool.accRewardTokenPerShare = pool.accRewardTokenPerShare.add(tokenReward.mul(1e12).div(totalStaked));
        pool.lastRewardBlock = block.number;
    }


    /// Deposit staking token into the contract to earn rewards.
    /// @dev Since this contract needs to be supplied with rewards we are
    ///  sending the balance of the contract if the pending rewards are higher
    /// @param _amount The amount of staking tokens to deposit
    function deposit(uint256 _pid, uint256 _amount, address _referrer) public {
        PoolInfo storage pool = poolInfo[_pid];
        UserInfo storage user = userInfo[_pid][msg.sender];
        updatePool(_pid);
        if (user.amount > 0) {
            uint256 pending = user.amount.mul(pool.accRewardTokenPerShare).div(1e12).sub(user.rewardDebt);
            if(pending > 0) {
                uint256 _withdrawFee = pending.mul(withdrawFee).div(100);
                if (_withdrawFee > 0) {
                    pending = pending.sub(_withdrawFee);
                    safeTransferReward(address(msg.sender), pool.rewardToken, _withdrawFee);
                }
                uint256 currentRewardBalance = rewardBalance(pool.rewardToken);
                if(currentRewardBalance > 0) {
                    uint256 referAmountLv1 = pending.mul(percentForReferLv1).div(100);
                    uint256 referAmountLv2 = pending.mul(percentForReferLv2).div(100);
                    _transferReferral(pool.rewardToken, referAmountLv1, referAmountLv2);

                    pending = pending.sub(referAmountLv1);

                    if(pending > currentRewardBalance) {
                        safeTransferReward(address(msg.sender), pool.rewardToken, currentRewardBalance);
                    } else {
                        safeTransferReward(address(msg.sender), pool.rewardToken, pending);
                    }

                    user.rewardDebtAtBlock = block.number;
                }
            }
        }
        if (_amount > 0) {
            // uint256 preStakeBalance = totalStakeTokenBalance();
            pool.stakeToken.safeTransferFrom(address(msg.sender), address(this), _amount);
            if (pool.depositFeeBP > 0){
                uint256 depositFee = _amount.mul(pool.depositFeeBP).div(10000);
                pool.stakeToken.safeTransfer(feeAddress, depositFee);
                user.amount = user.amount.add(_amount).sub(depositFee);
            } else {
                user.amount = user.amount.add(_amount);
            }
        }
        user.rewardDebt = user.amount.mul(pool.accRewardTokenPerShare).div(1e12);

        if (userRef[address(msg.sender)] == address(0) && _referrer != address(0) && _referrer != address(msg.sender)) {
            userRef[address(msg.sender)] = address(_referrer);
        }

        emit Deposit(msg.sender, _pid, _amount);
    }

    function _transferReferral(IBEP20 rewardToken, uint256 _referAmountLv1, uint256 _referAmountLv2) internal {
       
        address referrerLv1 = userRef[address(msg.sender)];
        uint256 referAmountForDev = 0;

        if (referrerLv1 != address(0)) {
            uint256 lpStaked = rewardToken.balanceOf(referrerLv1);
            if (lpStaked >= stakeAmountLv1 && _referAmountLv1>0 ) {
              
               if (rewardToken == pnixs) {
                   pnixs.mint(referrerLv1,  _referAmountLv1);
               } else {
                   rewardToken.safeTransfer(referrerLv1, _referAmountLv1);
               }
               
               referralAmountLv1[address(rewardToken)][address(referrerLv1)] = referralAmountLv1[address(rewardToken)][address(referrerLv1)].add(_referAmountLv1);
             
            } else {
               
                referAmountForDev = referAmountForDev.add(_referAmountLv1);
            }
        
            address referrerLv2 = userRef[referrerLv1];
            uint256 lpStaked2 = rewardToken.balanceOf(referrerLv2);
            if (referrerLv2 != address(0) && lpStaked2 >= stakeAmountLv2   && _referAmountLv2>0 ) {
             
                if (rewardToken == pnixs) {
                   pnixs.mint(referrerLv1,  _referAmountLv1);
                } else {
                    rewardToken.safeTransfer(referrerLv1, _referAmountLv1);
                }
                
                referralAmountLv2[address(rewardToken)][address(referrerLv2)] = referralAmountLv2[address(rewardToken)][address(referrerLv2)].add(_referAmountLv2);
              
            } else {
               
                referAmountForDev = referAmountForDev.add(_referAmountLv2);
            }
            
        } else {
            referAmountForDev = _referAmountLv1.add(_referAmountLv1);
        }

        if (referAmountForDev > 0) {
          
            if (rewardToken == pnixs) {
                pnixs.mint(devaddr,  referAmountForDev);
            } else {
                rewardToken.safeTransfer(devaddr, referAmountForDev);
            }
        }
    }

    /// Withdraw rewards and/or staked tokens. Pass a 0 amount to withdraw only rewards
    /// @param _amount The amount of staking tokens to withdraw
    function withdraw(uint256 _pid, uint256 _amount) public {
        PoolInfo storage pool = poolInfo[_pid];
        UserInfo storage user = userInfo[_pid][msg.sender];
        require(user.amount >= _amount, "withdraw: not good");
        updatePool(_pid);
        uint256 pending = user.amount.mul(pool.accRewardTokenPerShare).div(1e12).sub(user.rewardDebt);
        if(pending > 0) {
            uint256 _withdrawFee = pending.mul(withdrawFee).div(100);
            if (_withdrawFee > 0) {
                pending = pending.sub(_withdrawFee);
                safeTransferReward(address(msg.sender), pool.rewardToken, _withdrawFee);
            }
            uint256 currentRewardBalance = rewardBalance(pool.rewardToken);
            if(currentRewardBalance > 0) {
                uint256 referAmountLv1 = pending.mul(percentForReferLv1).div(100);
                uint256 referAmountLv2 = pending.mul(percentForReferLv2).div(100);
                _transferReferral(pool.rewardToken, referAmountLv1, referAmountLv2);

                pending = pending.sub(referAmountLv1);

                if(pending > currentRewardBalance) {
                    safeTransferReward(address(msg.sender), pool.rewardToken, currentRewardBalance);
                } else {
                    safeTransferReward(address(msg.sender), pool.rewardToken, pending);
                }
            }
        }
        if(_amount > 0) {
            user.amount = user.amount.sub(_amount);
            pool.stakeToken.safeTransfer(address(msg.sender), _amount);
        }

        user.rewardDebt = user.amount.mul(pool.accRewardTokenPerShare).div(1e12);

        emit Withdraw(msg.sender, _pid, _amount);
    }

    /* Emergency Functions */

    // Withdraw without caring about rewards. EMERGENCY ONLY.
    function emergencyWithdraw(uint256 _pid) external {
        PoolInfo storage pool = poolInfo[_pid];
        UserInfo storage user = userInfo[_pid][msg.sender];
        pool.stakeToken.safeTransfer(address(msg.sender), user.amount);
        user.amount = 0;
        user.rewardDebt = 0;
        emit EmergencyWithdraw(msg.sender, _pid, user.amount);
    }

    // Transfer Pnixs Token from MasterChef to _to Address
    function transferToken(address _to, uint256 _amount) public onlyOwner  {
   
         require(_to  != address(0), "transferToken: FORBIDDEN");
         safePnixsTransfer(_to, _amount);
       
    }

    // Safe PNIXS transfer function, just in case if rounding error causes pool to not have enough PNIXS.
    function safePnixsTransfer(address _to, uint256 _amount) internal {
        uint256 pnixsBal = pnixs.balanceOf(address(this));
        if (_amount > pnixsBal) {
            pnixs.transfer(_to, pnixsBal);
        } else {
            pnixs.transfer(_to, _amount);
        }
    }

    function registerRef(address _referrer) public{
         if (userRef[address(msg.sender)] == address(0) && _referrer != address(0) && _referrer != address(msg.sender)) {
            userRef[address(msg.sender)] = address(_referrer);
        }
    }

    // Update Minimum LPStake Amount to get Level Refer bonus
    function setAmountLPStakeLevelRefer(uint256 _stakeAmountLv1, uint256 _stakeAmountLv2) public onlyOwner {
        stakeAmountLv1 = _stakeAmountLv1;
        stakeAmountLv2 = _stakeAmountLv2;
       
    }

    // Update dev address by the previous dev.
    function dev(address _devaddr) public {
        require(msg.sender == devaddr, "dev: wut?");
        devaddr = _devaddr;
    }

    function setFeeAddress(address _feeAddress) public{
        require(msg.sender == feeAddress, "setFeeAddress: FORBIDDEN");
        feeAddress = _feeAddress;
    }

    // Update WithdrawFeeAddress address by the owner.
    function setWithdrawFeeAddress(address _withdrawfeeAddress) public onlyOwner{
        require(_withdrawfeeAddress  != address(0), "setWithdrawFeeAddress: FORBIDDEN");
        withdrawFeeAddress = _withdrawfeeAddress;
    }

    // Update withdrawFee, max withdrawFee=30%.
    function updateWithdrawFee(uint16 _amount) public onlyOwner {
        require(_amount <= 30, "set: invalid withdrawFee fee basis points"); // max withdrawFee=30%
        withdrawFee = _amount;
    }

    // Update PercentForReferLv1, max PercentForReferLv1=30%.
    function updatePercentForReferLv1(uint16 _amount) public onlyOwner {
        require(_amount <= 30, "set: invalid PercentForReferLv1 fee basis points"); // max PercentForReferLv1=30%
        percentForReferLv1 = _amount;
    }

    // Update PercentForReferLv2, max PercentForReferLv2=30%.
    function updatePercentForReferLv2(uint16 _amount) public onlyOwner {
        require(_amount <= 30, "set: invalid PercentForReferLv2 fee basis points"); // max PercentForReferLv2=30%
        percentForReferLv2 = _amount;
    }

    /// Obtain the reward balance of this contract
    /// @return wei balace of conract
    function rewardBalance(IBEP20 _rewardToken) public view returns (uint256) {
        if (_rewardToken == pnixs) {
            return pnixs.totalSupply();
        } else {
            return _rewardToken.balanceOf(address(this));
        }
    }

    /// @param _to address to send reward token to
    /// @param _amount value of reward token to transfer
    function safeTransferReward(address _to, IBEP20 _rewardToken, uint256 _amount) internal {
        if (_rewardToken == pnixs) {
            pnixs.mint(_to, _amount);
        } else {
            _rewardToken.safeTransfer(_to, _amount);
        }
    }

    /* Admin Functions */

    /// @param _rewardPerBlock The amount of reward tokens to be given per block
    function setRewardPerBlock(IBEP20 _rewardToken, uint256 _rewardPerBlock) external onlyOwner {
        uint256 aLength = allocInfo.length;
        for (uint256 aid = 0; aid < aLength; ++aid) {
            if (allocInfo[aid].rewardToken == _rewardToken) {
                allocInfo[aid].rewardPerBlock = _rewardPerBlock;
                break;
            }
        }
    }

}
