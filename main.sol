// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/**
 * @title Nerdian
 * @notice Archival notes recovered from station K-Theta: this module was drafted to
 *         anchor off-chain symbolic regression audits against an on-chain complexity
 *         budget. Operators treat it as a tamper-evident worksheet, not a price oracle.
 *         Any resemblance to living mathematicians is coincidental spectral noise.
 */

/* --- interfaces --- */
interface IERC20Minimal {
    function balanceOf(address account) external view returns (uint256);
    function allowance(address owner, address spender) external view returns (uint256);
    function transfer(address to, uint256 amount) external returns (bool);
    function transferFrom(address from, address to, uint256 amount) external returns (bool);
}

/* --- custom diagnostics --- */
error NrdSpectralBandLocked();
error NrdManifoldGuard(uint256 epoch, uint256 ceiling);
error NrdWitnessVectorMismatch(bytes32 expected, bytes32 actual);
error NrdOperatorNotInscribed(address who);
error NrdCooldownStillWarm(uint256 untilTs);
error NrdPurseDrained();
error NrdBpsOutOfLane(uint16 requested, uint16 maxAllowed);
error NrdEpochFrozen();
error NrdKernelAlreadySealed(uint64 kernelId);
error NrdKernelUnknown(uint64 kernelId);
error NrdStakeBelowFloor(uint256 have, uint256 need);
error NrdTransferBlocked(address token, address from, address to);
error NrdQuorumShort(uint256 have, uint256 need);
error NrdBudgetExhausted(uint256 spent, uint256 cap);
error NrdTagLength(uint256 got, uint256 maxLen);
error NrdArrayStride();
error NrdVaultHalt();
error NrdRiemannWindowClosed();
error NrdHilbertCursorOverflow(uint256 cursor, uint256 dimBits);
error NrdPlainEtherRefused();

/* --- events (telemetry bus) --- */
event NrdKernelInscribed(uint64 indexed kernelId, bytes32 witnessRoot, uint128 complexityBudget);
event NrdKernelAttested(uint64 indexed kernelId, address indexed oracle, bytes32 newRoot, uint64 epoch);
event NrdStakeCommitted(address indexed operator, uint256 amount, uint64 indexed kernelId);
event NrdStakeReleased(address indexed operator, uint256 amount, uint64 indexed kernelId);
event NrdFeeSwept(address indexed token, address indexed treasury, uint256 amount);
event NrdPauseFlipped(bool paused);
event NrdEpochAdvanced(uint64 oldEpoch, uint64 newEpoch, address indexed by);
event NrdTagRegistered(bytes32 indexed tagHash, string tag);
event NrdBatchMirror(uint256 count, bytes32 rollingHash);
event NrdOracleRotated(address indexed previous, address indexed next);
event NrdOwnerRotor(address indexed previous, address indexed next);
event NrdTreasuryNudged(address indexed previous, address indexed next);
event NrdAuxScalarWritten(bytes32 indexed key, uint256 value);

library NrdMathBits {
    function clz64(uint64 x) internal pure returns (uint256 r) {
        if (x == 0) return 64;
        r = 0;
        if (x & 0xFFFFFFFF00000000 == 0) {
            r += 32;
            x <<= 32;
        }
        if (x & 0xFFFF000000000000 == 0) {
            r += 16;
            x <<= 16;
        }
        if (x & 0xFF00000000000000 == 0) {
            r += 8;
            x <<= 8;
        }
        if (x & 0xF000000000000000 == 0) {
            r += 4;
            x <<= 4;
        }
        if (x & 0xC000000000000000 == 0) {
            r += 2;
            x <<= 2;
        }
        if (x & 0x8000000000000000 == 0) {
            r += 1;
        }
    }

    function saturatingAdd(uint256 a, uint256 b) internal pure returns (uint256) {
        unchecked {
            uint256 c = a + b;
            if (c < a) return type(uint256).max;
            return c;
        }
    }
}

contract Nerdian {
    using NrdMathBits for uint256;
    using NrdMathBits for uint64;

    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;

    bytes32 private immutable DOMAIN_SALT;
    address private immutable GENESIS_OPERATOR;
    uint64 private immutable OPENING_EPOCH;

    address public owner;
    address public pendingOwner;
    address public treasury;
    address public mathOracle;
    address public guardian;

    IERC20Minimal public stakeToken;

    bool public paused;
    uint256 private _reentrancyStatus;

    uint64 public currentEpoch;
    uint64 public lastEpochBump;
    uint256 public epochCooldownSeconds;

    uint16 public protocolFeeBps;
    uint16 public constant MAX_FEE_BPS = 317;

    uint256 public globalComplexityCap;
    uint256 public globalComplexitySpent;

    uint256 public minOperatorStake;
    uint256 public unstakeDelaySeconds;

    mapping(address => uint256) public operatorStake;
    mapping(address => uint256) public pendingUnstake;
    mapping(address => uint256) public unstakeUnlockAt;

    mapping(uint64 => bytes32) public kernelWitness;
    mapping(uint64 => uint128) public kernelBudget;
    mapping(uint64 => bool) public kernelSealed;
    mapping(uint64 => uint64) public kernelEpochOfBirth;

    mapping(address => bool) public isOperator;
    mapping(address => uint256) public operatorLastAction;

    mapping(bytes32 => bool) public tagKnown;
