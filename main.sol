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
        return globalComplexityCap - globalComplexitySpent;
    }

    function operatorPower(address who) external view returns (uint256) {
        return operatorStake[who] + pendingUnstake[who];
    }

    function tagFingerprint(string calldata tag) external pure returns (bytes32) {
        return keccak256(bytes(tag));
    }

    function batchTagMirror(string[] calldata tags) external returns (bytes32 rolling) {
        if (tags.length > MAX_BATCH) revert NrdArrayStride();
        rolling = bytes32(uint256(0xC0FFEE));
        for (uint256 i = 0; i < tags.length; i++) {
            _enforceTag(tags[i]);
            bytes32 th = keccak256(bytes(tags[i]));
            rolling = keccak256(abi.encodePacked(rolling, th));
        }
        emit NrdBatchMirror(tags.length, rolling);
    }

    function _enforceTag(string calldata tag) internal pure {
        bytes memory b = bytes(tag);
        if (b.length == 0 || b.length > MAX_TAG_UTF8) revert NrdTagLength(b.length, MAX_TAG_UTF8);
    }

    /* --- extended worksheet (padding with real logic) --- */
    function chebyshevT(uint256 n, int256 x) external pure returns (int256 y) {
        if (n == 0) return int256(1);
        if (n == 1) return x;
        int256 t0 = int256(1);
        int256 t1 = x;
        for (uint256 k = 2; k <= n; k++) {
            y = 2 * t1 * x / int256(1) - t0;
            t0 = t1;
            t1 = y;
        }
        y = t1;
    }

    function bernoulliB2n(uint256 n) external pure returns (uint256) {
        if (n > 12) revert NrdManifoldGuard(n, 12);
        uint256[13] memory table = [
            uint256(1),
            uint256(1),
            uint256(1),
            uint256(1),
            uint256(1),
            uint256(5),
            uint256(691),
            uint256(7),
            uint256(3617),
            uint256(43867),
            uint256(174611),
            uint256(77683),
            uint256(236364091)
        ];
        return table[n];
    }

    function lucasMod(uint256 index, uint256 mod) external pure returns (uint256) {
        if (mod < 3) revert NrdManifoldGuard(mod, 3);
        if (index == 0) return 2 % mod;
        if (index == 1) return 1 % mod;
        uint256 a = 2 % mod;
        uint256 b = 1 % mod;
        for (uint256 i = 2; i <= index; i++) {
            uint256 c = (a + b) % mod;
            a = b;
            b = c;
        }
        return b;
    }

    function sternBrocotDepth(uint256 p, uint256 q) external pure returns (uint256 depth) {
        if (q == 0) revert NrdManifoldGuard(q, 1);
        depth = 0;
        while (p != 1 || q != 1) {
            if (p > q) {
                p -= q;
            } else {
                q -= p;
            }
            depth++;
            if (depth > 512) revert NrdHilbertCursorOverflow(depth, 512);
        }
    }

    function mertensWindow(uint256 upTo) external pure returns (int256 m) {
        if (upTo > 241) revert NrdRiemannWindowClosed();
        int256 acc = 0;
        for (uint256 n = 1; n <= upTo; n++) {
            acc += int256(_mobiusSmall(n));
        }
        m = acc;
    }

    function _mobiusSmall(uint256 n) private pure returns (int256) {
        if (n == 1) return 1;
        uint256 sq = 0;
        uint256 t = n;
        uint256 primes = 0;
        for (uint256 d = 2; d * d <= t; d++) {
            if (t % d == 0) {
                primes++;
                while (t % d == 0) {
                    t /= d;
                    sq++;
                    if (sq > 1) return 0;
                }
            }
        }
        if (t > 1) {
            primes++;
        }
        if (primes % 2 == 0) return 1;
        return -1;
    }

    function dilateUint(uint256 x, uint256 num, uint256 den) external pure returns (uint256) {
        if (den == 0) revert NrdManifoldGuard(den, 1);
        return (x * num) / den;
    }

    function popcount256(uint256 x) external pure returns (uint256 c) {
        while (x != 0) {
            x &= (x - 1);
            c++;
        }
    }

    function grayCode(uint256 x) external pure returns (uint256) {
        return x ^ (x >> 1);
    }

    function inverseGray(uint256 g) external pure returns (uint256) {
        uint256 x = g;
        g >>= 1;
        while (g != 0) {
            x ^= g;
            g >>= 1;
        }
        return x;
    }

    function collatzStepsBounded(uint256 seed, uint256 maxSteps) external pure returns (uint256 steps, uint256 last) {
        uint256 n = seed;
        steps = 0;
        while (n != 1 && steps < maxSteps) {
            if (n & 1 == 0) {
                unchecked {
                    n >>= 1;
                }
            } else {
                n = 3 * n + 1;
            }
            steps++;
        }
        last = n;
    }

    function fibModStream(uint256 count, uint256 mod) external pure returns (uint256 h) {
        if (mod == 0) revert NrdManifoldGuard(mod, 1);
        if (count > MAX_BATCH) revert NrdArrayStride();
        uint256 a = 0;
        uint256 b = 1;
        h = keccak256(abi.encodePacked(a, b));
        for (uint256 i = 0; i < count; i++) {
            uint256 c = (a + b) % mod;
            a = b;
            b = c;
            h = keccak256(abi.encodePacked(h, c));
        }
    }

    function triangularRootFloor(uint256 s) external pure returns (uint256 n) {
        uint256 lo = 0;
        uint256 hi = 2 ** 128;
        while (lo < hi) {
            uint256 mid = (lo + hi + 1) >> 1;
            uint256 t = mid * (mid + 1) / 2;
            if (t <= s) {
                lo = mid;
            } else {
                hi = mid - 1;
            }
        }
        n = lo;
    }

    function cantorPair(uint256 a, uint256 b) external pure returns (uint256) {
        return (a + b) * (a + b + 1) / 2 + b;
    }

    function szudzikPair(uint256 a, uint256 b) external pure returns (uint256) {
        if (a < b) return b * b + a;
        return a * a + a + b;
    }

    function isProbableSemiprime(uint256 x) external pure returns (bool maybe) {
        if (x < 4) return false;
        uint256 factors = 0;
        uint256 t = x;
        for (uint256 d = 2; d * d <= t && factors < 3; d++) {
            while (t % d == 0) {
                t /= d;
                factors++;
                if (factors > 2) return false;
            }
        }
        if (t > 1) factors++;
        maybe = (factors == 2);
    }

    function eulerTotientSmall(uint256 n) external pure returns (uint256 phi) {
        if (n == 0) return 0;
        phi = n;
        uint256 t = n;
        for (uint256 p = 2; p * p <= t; p++) {
            if (t % p == 0) {
                while (t % p == 0) {
                    t /= p;
                }
                phi -= phi / p;
            }
        }
        if (t > 1) phi -= phi / t;
    }

    function jacobiSymbol(uint256 a, uint256 n) external pure returns (int256) {
        if (n == 0 || (n & 1) == 0) revert NrdManifoldGuard(n, 1);
        int256 j = 1;
        uint256 aa = a % n;
        uint256 nn = n;
        while (aa != 0) {
            while ((aa & 1) == 0) {
                aa >>= 1;
                if ((nn & 7) == 3 || (nn & 7) == 5) j = -j;
            }
            (aa, nn) = (nn, aa);
            if ((aa & 3) == 3 && (nn & 3) == 3) j = -j;
            aa %= nn;
        }
        if (nn == 1) return j;
        return 0;
    }

    function ramanujanTauSmall(uint256 n) external pure returns (int256) {
        if (n > 23) revert NrdManifoldGuard(n, 23);
        int256[24] memory tbl = [
            int256(0),
            1,
            -24,
            252,
            -1472,
            4830,
            -6048,
            -16744,
            84480,
            -113643,
            -115920,
            534612,
            -370944,
            -1228896,
            3627628,
            1617870,
            -10749952,
            9472900,
            6842292,
            -29211840,
            -52878671,
            64260000,
            38731776,
            -545607520
        ];
        return tbl[n];
    }

    function partitionPSmall(uint256 n) external pure returns (uint256) {
        if (n > 40) revert NrdManifoldGuard(n, 40);
        uint256[41] memory tbl = [
            uint256(1),
            1,
            2,
            3,
            5,
            7,
            11,
            15,
            22,
            30,
            42,
            56,
            77,
            101,
            135,
            176,
            231,
            297,
            385,
            490,
            627,
            792,
            1002,
            1255,
            1575,
            1958,
            2436,
            3010,
            3718,
            4555,
            5604,
            6842,
            8349,
            10143,
            12310,
            14883,
            17977,
            21637,
            26015,
            31185,
            37338
        ];
        return tbl[n];
    }

    function vanDerCorput(uint256 bits, uint256 index) external pure returns (uint256) {
        if (bits > 64) revert NrdHilbertCursorOverflow(bits, 64);
        uint256 x = index;
        uint256 denom = 1 << bits;
        uint256 num = 0;
        uint256 b = bits;
        while (b > 0) {
            num <<= 1;
            num |= (x & 1);
            x >>= 1;
            b--;
        }
        return (num << bits) / denom;
    }

    function continuedFracConvergent(uint256 num, uint256 den, uint256 steps)
        external
        pure
        returns (uint256 pOut, uint256 qOut)
    {
        if (den == 0) revert NrdManifoldGuard(den, 1);
        uint256 p0 = 0;
        uint256 p1 = 1;
        uint256 q0 = 1;
        uint256 q1 = 0;
        uint256 a = num;
        uint256 b = den;
        for (uint256 s = 0; s < steps && b != 0; s++) {
            uint256 t = a / b;
            uint256 p2 = t * p1 + p0;
            uint256 q2 = t * q1 + q0;
            (a, b) = (b, a % b);
            (p0, p1) = (p1, p2);
            (q0, q1) = (q1, q2);
        }
        pOut = p1;
        qOut = q1;
    }

    function ackermannBounded(uint256 m, uint256 n, uint256 gasCap) external pure returns (uint256 v) {
        if (m > 3 || n > 12) revert NrdManifoldGuard(m + n, 15);
        uint256 g = gasCap;
        if (m == 0) return n + 1;
        if (m == 1) return n + 2;
        if (m == 2) return 2 * n + 3;
        if (m == 3) {
            v = 5;
            for (uint256 i = 0; i < n && g > 0; i++) {
                v = (v << 1) + 3;
                g--;
            }
            return v;
        }
        revert NrdManifoldGuard(m, 3);
    }

    function primePiUpper(uint256 x) external pure returns (uint256) {
        if (x < 2) return 0;
        uint256 num = x;
        uint256 den = 9;
        uint256 lg = 0;
        uint256 t = x;
        while (t > 1) {
            t >>= 1;
            lg++;
        }
        return (num * lg) / den + 3;
    }

    function harmonicPartial(uint256 n) external pure returns (uint256 scaled) {
        if (n > 88) revert NrdManifoldGuard(n, 88);
        uint256 num = 0;
        uint256 den = 1;
        for (uint256 i = 1; i <= n; i++) {
            num = num * i + den;
            den *= i;
            uint256 g = _gcd(num, den);
            num /= g;
            den /= g;
        }
        scaled = (num * 1e18) / den;
    }

    function _gcd(uint256 a, uint256 b) private pure returns (uint256) {
        while (b != 0) {
            uint256 t = a % b;
            a = b;
            b = t;
        }
        return a;
    }

    function digitRoot(uint256 x) external pure returns (uint256) {
        if (x == 0) return 0;
        uint256 r = x % 9;
        return r == 0 ? 9 : r;
    }

    function sqrtFloor(uint256 y) external pure returns (uint256 z) {
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

    function isqrtNewton(uint256 n) external pure returns (uint256 r) {
        if (n == 0) return 0;
        r = n;
        uint256 x = n / 2 + 1;
        while (x < r) {
            r = x;
            x = (n / x + x) / 2;
        }
    }

    function cbrtFloor(uint256 x) external pure returns (uint256 y) {
        uint256 lo = 0;
        uint256 hi = 2 ** 86;
        while (lo < hi) {
            uint256 mid = (lo + hi + 1) >> 1;
            uint256 m3;
            unchecked {
                m3 = mid * mid * mid;
            }
            if (m3 <= x) lo = mid;
            else hi = mid - 1;
        }
        y = lo;
    }

    function lcmMany(uint256[] calldata vals) external pure returns (uint256) {
        if (vals.length == 0) revert NrdArrayStride();
        if (vals.length > MAX_BATCH) revert NrdArrayStride();
        uint256 l = vals[0];
        for (uint256 i = 1; i < vals.length; i++) {
            uint256 a = l;
            uint256 b = vals[i];
            if (b == 0) revert NrdManifoldGuard(b, 1);
            uint256 g = _gcd(a, b);
            l = a / g * b;
        }
        return l;
    }

    function gcdMany(uint256[] calldata vals) external pure returns (uint256) {
        if (vals.length == 0) revert NrdArrayStride();
        uint256 g = vals[0];
        for (uint256 i = 1; i < vals.length; i++) {
            g = _gcd(g, vals[i]);
        }
        return g;
    }

    function rollingXorDigest(uint256[] calldata words) external pure returns (uint256 x) {
        if (words.length > MAX_BATCH) revert NrdArrayStride();
        for (uint256 i = 0; i < words.length; i++) {
            x ^= words[i];
            x = (x << 1) | (x >> 255);
        }
    }

    function modularExp(uint256 base, uint256 e, uint256 mod) external pure returns (uint256) {
        if (mod <= 1) revert NrdManifoldGuard(mod, 2);
        uint256 result = 1;
        base %= mod;
        uint256 exp = e;
        while (exp > 0) {
            if (exp & 1 == 1) {
                result = mulmod(result, base, mod);
            }
            base = mulmod(base, base, mod);
            exp >>= 1;
        }
        return result;
    }

    function blumBlumShubStep(uint256 x, uint256 M) external pure returns (uint256) {
        if (M < 4) revert NrdManifoldGuard(M, 4);
        return mulmod(x, x, M);
    }

    function logisticMapQ16(uint256 r, uint256 x, uint256 iters) external pure returns (uint256) {
        if (iters > 60) revert NrdManifoldGuard(iters, 60);
        uint256 v = x;
        for (uint256 i = 0; i < iters; i++) {
            v = (r * v * (65536 - v)) / (65536 * 65536);
        }
        return v;
    }

    function householderReflectPacked(uint256 v0, uint256 v1, uint256 u0, uint256 u1, uint256 denom)
        external
        pure
        returns (uint256 w0, uint256 w1)
    {
        if (denom == 0) revert NrdManifoldGuard(denom, 1);
        uint256 dot = v0 * u0 + v1 * u1;
        w0 = v0 - (2 * dot * u0) / denom;
        w1 = v1 - (2 * dot * u1) / denom;
    }

    function polygonAreaShoelace(int256[] calldata xs, int256[] calldata ys)
        external
        pure
        returns (int256 area2)
    {
        if (xs.length != ys.length) revert NrdArrayStride();
        if (xs.length < 3 || xs.length > MAX_BATCH) revert NrdArrayStride();
        uint256 n = xs.length;
        for (uint256 i = 0; i < n; i++) {
            uint256 j = (i + 1) % n;
            area2 += xs[i] * ys[j];
            area2 -= xs[j] * ys[i];
        }
        if (area2 < 0) area2 = -area2;
    }

    function bezierQuadY(uint256 t, uint256 y0, uint256 y1, uint256 y2) external pure returns (uint256) {
        uint256 u = 1000 - t;
        return (u * u * y0 + 2 * u * t * y1 + t * t * y2) / 1_000_000;
    }

    function catmullRom1D(uint256 p0, uint256 p1, uint256 p2, uint256 p3, uint256 t) external pure returns (uint256) {
        uint256 t2 = t * t;
        uint256 t3 = t2 * t;
        return (2 * p1 + (-p0 + p2) * t + (2 * p0 - 5 * p1 + 4 * p2 - p3) * t2 + (-p0 + 3 * p1 - 3 * p2 + p3) * t3) / 2;
    }

    function softmax2(uint256 a, uint256 b, uint256 temp) external pure returns (uint256 sa, uint256 sb) {
        if (temp == 0) revert NrdManifoldGuard(temp, 1);
        uint256 ea = a / temp;
        uint256 eb = b / temp;
        uint256 denom = ea + eb + 1;
        sa = (ea * 1e18) / denom;
        sb = (eb * 1e18) / denom;
    }

    function entropyBernoulli(uint256 pNum, uint256 pDen) external pure returns (uint256 bitsScaled) {
        if (pDen == 0) revert NrdManifoldGuard(pDen, 1);
        if (pNum > pDen) revert NrdManifoldGuard(pNum, pDen);
        uint256 qNum = pDen - pNum;
        uint256 h = 0;
        if (pNum > 0) {
            h += (pNum * _log2Approx(pDen * 1e18 / pNum)) / pDen;
        }
        if (qNum > 0) {
            h += (qNum * _log2Approx(pDen * 1e18 / qNum)) / pDen;
        }
        bitsScaled = h;
    }

    function _log2Approx(uint256 x) private pure returns (uint256) {
        uint256 r = 0;
        uint256 v = x;
        for (uint256 i = 0; i < 64; i++) {
            if (v >= 2 * 1e18) {
                v /= 2;
                r += 1e18;
            } else {
                break;
            }
        }
        return r * 1e18;
    }

    function reservoirSampleHash(bytes32 seed, uint256[] calldata weights) external pure returns (uint256 idx) {
        if (weights.length == 0) revert NrdArrayStride();
        if (weights.length > MAX_BATCH) revert NrdArrayStride();
        uint256 acc = uint256(seed) % weights[0];
        idx = 0;
        for (uint256 i = 1; i < weights.length; i++) {
            acc += weights[i];
            uint256 roll = uint256(keccak256(abi.encodePacked(seed, i))) % (acc + 1);
            if (roll < weights[i]) {
                idx = i;
            }
        }
    }

    function welfordOnline(int256[] calldata stream) external pure returns (int256 mean, int256 varSample) {
        if (stream.length == 0) revert NrdArrayStride();
        int256 n = 0;
        int256 M = 0;
        int256 S = 0;
        for (uint256 i = 0; i < stream.length; i++) {
            n += 1;
            int256 x = stream[i];
            int256 d = x - M;
            M += d / n;
            S += d * (x - M);
        }
        mean = M;
        if (n > 1) {
            varSample = S / (n - 1);
        }
    }

    function kahanSummation(int256[] calldata terms) external pure returns (int256 sum) {
        int256 c = 0;
        for (uint256 i = 0; i < terms.length; i++) {
            int256 y = terms[i] - c;
            int256 t = sum + y;
            c = (t - sum) - y;
            sum = t;
        }
    }

    function hornerPoly(int256[] calldata coeffs, int256 x) external pure returns (int256 y) {
        if (coeffs.length == 0) revert NrdArrayStride();
        y = coeffs[0];
        for (uint256 i = 1; i < coeffs.length; i++) {
            y = y * x + coeffs[i];
        }
    }

    function newtonSqrtIter(uint256 S, uint256 x0, uint256 iters) external pure returns (uint256 x) {
        x = x0;
        if (S == 0) return 0;
        for (uint256 i = 0; i < iters; i++) {
            x = (x + S / x) >> 1;
        }
    }

    function bisectionRoot(int256 lo, int256 hi, int256 fa, int256 fb) external pure returns (int256 mid) {
        if (fa * fb > 0) revert NrdWitnessVectorMismatch(bytes32(uint256(fa)), bytes32(uint256(fb)));
        for (uint256 i = 0; i < 48; i++) {
            mid = (lo + hi) >> 1;
            if (mid == lo || mid == hi) break;
            int256 fm = mid;
            if (fa * fm <= 0) {
                hi = mid;
                fb = fm;
            } else {
                lo = mid;
                fa = fm;
            }
        }
    }

    function simpsonIntegral(uint256 a, uint256 b, uint256 fa, uint256 fb, uint256 fc) external pure returns (uint256) {
        return ((b - a) * (fa + 4 * fc + fb)) / 6;
    }

    function trapezoidStack(uint256[] calldata ys, uint256 h) external pure returns (uint256 area) {
        if (ys.length < 2 || ys.length > MAX_BATCH) revert NrdArrayStride();
        for (uint256 i = 0; i < ys.length - 1; i++) {
            area += h * (ys[i] + ys[i + 1]) / 2;
        }
    }

    function rungeKutta4Step(int256 x, int256 y, int256 h, int256 k1, int256 k2, int256 k3, int256 k4)
        external
        pure
        returns (int256 yNext, int256 xNext)
    {
        yNext = y + (h * (k1 + 2 * k2 + 2 * k3 + k4)) / 6;
        xNext = x + h;
    }

    function conv1dReflect(uint256[] calldata signal, uint256[] calldata kernel)
        external
        pure
        returns (uint256[] memory out)
    {
        if (signal.length == 0 || kernel.length == 0) revert NrdArrayStride();
        if (kernel.length > signal.length) revert NrdArrayStride();
        uint256 n = signal.length;
        uint256 m = kernel.length;
        out = new uint256[](n);
        uint256 pad = m / 2;
        for (uint256 i = 0; i < n; i++) {
            uint256 acc = 0;
            for (uint256 j = 0; j < m; j++) {
                int256 idx = int256(i + j) - int256(pad);
                if (idx < 0) idx = -idx;
                if (uint256(idx) >= n) idx = int256(2 * int256(n - 1) - idx);
                acc += signal[uint256(idx)] * kernel[j];
