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
    mapping(bytes32 => uint256) public tagUsageCount;

    mapping(bytes32 => uint256) public auxScalar;

    uint64 public nextKernelId;

    uint256 public constant MAX_TAG_UTF8 = 96;
    uint256 public constant MAX_BATCH = 41;

    modifier onlyOwner() {
        if (msg.sender != owner) revert NrdSpectralBandLocked();
        _;
    }

    modifier onlyOracle() {
        if (msg.sender != mathOracle) revert NrdOperatorNotInscribed(msg.sender);
        _;
    }

    modifier onlyGuardian() {
        if (msg.sender != guardian) revert NrdOperatorNotInscribed(msg.sender);
        _;
    }

    modifier whenNotPaused() {
        if (paused) revert NrdVaultHalt();
        _;
    }

    modifier nonReentrant() {
        if (_reentrancyStatus == _ENTERED) revert NrdPurseDrained();
        _reentrancyStatus = _ENTERED;
        _;
        _reentrancyStatus = _NOT_ENTERED;
    }

    constructor(
        address stakeToken_,
        address treasury_,
        address mathOracle_,
        address guardian_,
        address owner_,
        uint256 minOperatorStake_,
        uint256 unstakeDelaySeconds_,
        uint256 globalComplexityCap_,
        uint16 protocolFeeBps_,
        uint256 epochCooldownSeconds_
    ) {
        if (stakeToken_ == address(0)) revert NrdTransferBlocked(stakeToken_, address(0), address(0));
        if (treasury_ == address(0)) revert NrdTransferBlocked(IERC20Minimal(stakeToken_), treasury_, treasury_);
        if (mathOracle_ == address(0)) revert NrdOperatorNotInscribed(mathOracle_);
        if (guardian_ == address(0)) revert NrdOperatorNotInscribed(guardian_);
        if (owner_ == address(0)) revert NrdOperatorNotInscribed(owner_);
        if (protocolFeeBps_ > MAX_FEE_BPS) revert NrdBpsOutOfLane(protocolFeeBps_, MAX_FEE_BPS);

        stakeToken = IERC20Minimal(stakeToken_);
        treasury = treasury_;
        mathOracle = mathOracle_;
        guardian = guardian_;
        owner = owner_;
        pendingOwner = address(0);

        minOperatorStake = minOperatorStake_;
        unstakeDelaySeconds = unstakeDelaySeconds_;
        globalComplexityCap = globalComplexityCap_;
        protocolFeeBps = protocolFeeBps_;
        epochCooldownSeconds = epochCooldownSeconds_;

        currentEpoch = 1;
        lastEpochBump = uint64(block.timestamp);
        OPENING_EPOCH = currentEpoch;

        DOMAIN_SALT = keccak256("Nerdian.tensorSheaf.v7");
        GENESIS_OPERATOR = owner_;

        _reentrancyStatus = _NOT_ENTERED;
        nextKernelId = 1;

        auxScalar[keccak256("Nerdian.bootstrap.scalarA")] = 0x9E3779B97F4A7C15;
        auxScalar[keccak256("Nerdian.bootstrap.scalarB")] = 0xC2B2AE3D27D4EB4F;
    }

    /* --- ownership (two-step) --- */
    function transferOwnership(address next) external onlyOwner {
        pendingOwner = next;
    }

    function acceptOwnership() external {
        address p = pendingOwner;
        if (p == address(0)) revert NrdSpectralBandLocked();
        if (msg.sender != p) revert NrdOperatorNotInscribed(msg.sender);
        address old = owner;
        owner = p;
        pendingOwner = address(0);
        emit NrdOwnerRotor(old, owner);
    }

    function renounceOwnership() external onlyOwner {
        owner = address(0);
        pendingOwner = address(0);
    }

    /* --- admin surface --- */
    function setTreasury(address next) external onlyOwner {
        if (next == address(0)) revert NrdTransferBlocked(address(stakeToken), treasury, next);
        address prev = treasury;
        treasury = next;
        emit NrdTreasuryNudged(prev, next);
    }

    function setMathOracle(address next) external onlyOwner {
        if (next == address(0)) revert NrdOperatorNotInscribed(next);
        address prev = mathOracle;
        mathOracle = next;
        emit NrdOracleRotated(prev, next);
    }

    function setGuardian(address next) external onlyOwner {
        if (next == address(0)) revert NrdOperatorNotInscribed(next);
        guardian = next;
    }

    function setProtocolFeeBps(uint16 bps) external onlyOwner {
        if (bps > MAX_FEE_BPS) revert NrdBpsOutOfLane(bps, MAX_FEE_BPS);
        protocolFeeBps = bps;
    }

    function setMinOperatorStake(uint256 v) external onlyOwner {
        minOperatorStake = v;
    }

    function setUnstakeDelay(uint256 v) external onlyOwner {
        unstakeDelaySeconds = v;
    }

    function setGlobalComplexityCap(uint256 v) external onlyOwner {
        globalComplexityCap = v;
    }

    function setEpochCooldown(uint256 v) external onlyOwner {
        epochCooldownSeconds = v;
    }

    function flipPause() external onlyGuardian {
        paused = !paused;
        emit NrdPauseFlipped(paused);
    }

    function writeAuxScalar(bytes32 key, uint256 value) external onlyOwner {
        auxScalar[key] = value;
        emit NrdAuxScalarWritten(key, value);
    }

    /* --- epoch rail --- */
    function bumpEpoch() external onlyOracle whenNotPaused {
        if (block.timestamp < uint256(lastEpochBump) + epochCooldownSeconds) {
            revert NrdCooldownStillWarm(uint256(lastEpochBump) + epochCooldownSeconds);
        }
        uint64 old = currentEpoch;
        unchecked {
            currentEpoch += 1;
        }
        lastEpochBump = uint64(block.timestamp);
        emit NrdEpochAdvanced(old, currentEpoch, msg.sender);
    }

    /* --- operator enrollment --- */
    function enrollOperator(address who) external onlyOwner whenNotPaused {
        if (who == address(0)) revert NrdOperatorNotInscribed(who);
        isOperator[who] = true;
        operatorLastAction[who] = block.timestamp;
    }

    function revokeOperator(address who) external onlyOwner {
        isOperator[who] = false;
    }

    /* --- kernels --- */
    function inscribeKernel(bytes32 witnessRoot, uint128 complexityBudget, string calldata tag)
        external
        whenNotPaused
        nonReentrant
        returns (uint64 kernelId)
    {
        if (!isOperator[msg.sender]) revert NrdOperatorNotInscribed(msg.sender);
        _enforceTag(tag);
        bytes32 tagHash = keccak256(bytes(tag));
        if (!tagKnown[tagHash]) {
            tagKnown[tagHash] = true;
            emit NrdTagRegistered(tagHash, tag);
        }
        tagUsageCount[tagHash] += 1;

        uint256 projected = NrdMathBits.saturatingAdd(globalComplexitySpent, uint256(complexityBudget));
        if (projected > globalComplexityCap) revert NrdBudgetExhausted(projected, globalComplexityCap);

        kernelId = nextKernelId;
        unchecked {
            nextKernelId += 1;
        }
        kernelWitness[kernelId] = witnessRoot;
        kernelBudget[kernelId] = complexityBudget;
        kernelSealed[kernelId] = false;
        kernelEpochOfBirth[kernelId] = currentEpoch;

        globalComplexitySpent = projected;
        operatorLastAction[msg.sender] = block.timestamp;

        emit NrdKernelInscribed(kernelId, witnessRoot, complexityBudget);
    }

    function attestKernel(uint64 kernelId, bytes32 newRoot) external onlyOracle whenNotPaused {
        if (kernelId == 0 || kernelId >= nextKernelId) revert NrdKernelUnknown(kernelId);
        if (kernelSealed[kernelId]) revert NrdKernelAlreadySealed(kernelId);
        kernelWitness[kernelId] = newRoot;
        emit NrdKernelAttested(kernelId, msg.sender, newRoot, currentEpoch);
    }

    function sealKernel(uint64 kernelId) external onlyOracle whenNotPaused {
        if (kernelId == 0 || kernelId >= nextKernelId) revert NrdKernelUnknown(kernelId);
        kernelSealed[kernelId] = true;
    }

    /* --- staking --- */
    function commitStake(uint256 amount, uint64 kernelId) external whenNotPaused nonReentrant {
        if (!isOperator[msg.sender]) revert NrdOperatorNotInscribed(msg.sender);
        if (kernelId != 0 && (kernelId >= nextKernelId || kernelSealed[kernelId])) revert NrdKernelUnknown(kernelId);
        if (amount == 0) revert NrdStakeBelowFloor(amount, 1);

        uint256 bal = stakeToken.balanceOf(msg.sender);
        if (bal < amount) revert NrdStakeBelowFloor(bal, amount);
        uint256 alw = stakeToken.allowance(msg.sender, address(this));
        if (alw < amount) revert NrdStakeBelowFloor(alw, amount);

        bool ok = stakeToken.transferFrom(msg.sender, address(this), amount);
        if (!ok) revert NrdTransferBlocked(address(stakeToken), msg.sender, address(this));

        operatorStake[msg.sender] += amount;
        if (operatorStake[msg.sender] < minOperatorStake) revert NrdStakeBelowFloor(operatorStake[msg.sender], minOperatorStake);

        emit NrdStakeCommitted(msg.sender, amount, kernelId);
        operatorLastAction[msg.sender] = block.timestamp;
    }

    function requestUnstake(uint256 amount) external whenNotPaused nonReentrant {
        if (amount == 0) revert NrdStakeBelowFloor(amount, 1);
        uint256 st = operatorStake[msg.sender];
        if (st < amount) revert NrdStakeBelowFloor(st, amount);

        operatorStake[msg.sender] = st - amount;
        pendingUnstake[msg.sender] += amount;
        unstakeUnlockAt[msg.sender] = block.timestamp + unstakeDelaySeconds;
    }

    function finalizeUnstake(uint64 kernelId) external whenNotPaused nonReentrant {
        uint256 pend = pendingUnstake[msg.sender];
        if (pend == 0) revert NrdPurseDrained();
        if (block.timestamp < unstakeUnlockAt[msg.sender]) {
            revert NrdCooldownStillWarm(unstakeUnlockAt[msg.sender]);
        }

        uint256 fee = (pend * uint256(protocolFeeBps)) / 10_000;
        uint256 net = pend - fee;

        pendingUnstake[msg.sender] = 0;
        unstakeUnlockAt[msg.sender] = 0;

        if (fee > 0) {
            bool okFee = stakeToken.transfer(treasury, fee);
            if (!okFee) revert NrdTransferBlocked(address(stakeToken), address(this), treasury);
            emit NrdFeeSwept(address(stakeToken), treasury, fee);
        }
        bool okNet = stakeToken.transfer(msg.sender, net);
        if (!okNet) revert NrdTransferBlocked(address(stakeToken), address(this), msg.sender);

        emit NrdStakeReleased(msg.sender, net, kernelId);
    }

    /* --- rescue (tokens stuck, not stakeToken re-entrancy) --- */
    function rescueERC20(address token, address to, uint256 amount) external onlyOwner nonReentrant {
        if (token == address(stakeToken)) revert NrdTransferBlocked(token, address(this), to);
        if (to == address(0)) revert NrdTransferBlocked(token, address(this), to);
        IERC20Minimal t = IERC20Minimal(token);
        bool ok = t.transfer(to, amount);
        if (!ok) revert NrdTransferBlocked(token, address(this), to);
    }

    /* --- pure / view helpers (symbolic worksheet) --- */
    function foldComplexity(uint64[] calldata weights, uint64[] calldata exponents)
        external
        pure
        returns (uint256 acc)
    {
        if (weights.length != exponents.length) revert NrdArrayStride();
        if (weights.length > MAX_BATCH) revert NrdArrayStride();
        acc = 0;
        for (uint256 i = 0; i < weights.length; i++) {
            uint256 term = uint256(weights[i]);
            uint256 e = uint256(exponents[i]);
            if (e > 7) revert NrdManifoldGuard(e, 7);
            uint256 local = term;
            for (uint256 k = 1; k < e; k++) {
                local *= term;
            }
            acc = NrdMathBits.saturatingAdd(acc, local);
        }
    }

    function hilbertSlot(uint256 dimBits, uint256 x, uint256 y) external pure returns (uint256 slot) {
        if (dimBits == 0 || dimBits > 32) revert NrdHilbertCursorOverflow(dimBits, 32);
        uint256 maxC = (uint256(1) << dimBits) - 1;
        if (x > maxC || y > maxC) revert NrdHilbertCursorOverflow(x, maxC);

        slot = 0;
        for (uint256 s = dimBits; s > 0; ) {
            unchecked {
                s -= 1;
            }
            uint256 rx = (x >> s) & 1;
            uint256 ry = (y >> s) & 1;
            slot <<= 2;
            slot |= (rx * 3) ^ ry;
            if (ry == 0) {
                if (rx == 1) {
                    x = maxC - x;
                    y = maxC - y;
                }
                (x, y) = (y, x);
            }
        }
    }

    function domainDigest(bytes32 kernelSalt, uint64 kernelId, address operatorHint)
        external
        view
        returns (bytes32)
    {
        return keccak256(abi.encode(DOMAIN_SALT, kernelSalt, kernelId, operatorHint, GENESIS_OPERATOR, OPENING_EPOCH));
    }

    function rollingBatchHash(bytes32 seed, uint256[] calldata limbs) external pure returns (bytes32 h) {
        if (limbs.length > MAX_BATCH) revert NrdArrayStride();
        h = seed;
        for (uint256 i = 0; i < limbs.length; i++) {
            h = keccak256(abi.encodePacked(h, limbs[i]));
        }
    }

    function witnessGlue(uint64 kernelId, bytes32 left, bytes32 right) external view returns (bytes32) {
        if (kernelId == 0 || kernelId >= nextKernelId) revert NrdKernelUnknown(kernelId);
        return keccak256(abi.encodePacked(kernelWitness[kernelId], left, right, currentEpoch));
    }

    function complexityHeadroom() external view returns (uint256) {
        if (globalComplexitySpent >= globalComplexityCap) return 0;
