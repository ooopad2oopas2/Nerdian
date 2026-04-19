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
