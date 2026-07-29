#include "operation.h"
#include "../IO/out_dot.h"

// #define BRAVE_DD_OPERATION_TRACE
// #define BRAVE_DD_PRINT_RELATIONS
// #define BRAVE_DD_CONCRETIZATION_HELP_CACHE  // better not turn it on
#define BRAVE_DD_SAT_STRATEGY_1
// #define BRAVE_DD_SAT_STRATEGY_2

/* Thresholds to check if sweep and enlarge needed */
// static float thresholdsSweep = 0.66f;
static float thresholdsEnlarge = 0.33f;

using namespace BRAVE_DD;
// ******************************************************************
// *                                                                *
// *                                                                *
// *                      Operation  methods                        *
// *                                                                *
// *                                                                *
// ******************************************************************

Operation::Operation()
{
    //
}
Operation::~Operation()
{
    //
}

// ******************************************************************
// *                                                                *
// *                    UnaryOperation  class                       *
// *                                                                *
// ******************************************************************
UnaryOperation::UnaryOperation(UnaryOperationType type, Forest* source, Forest* target)
:opType(type)
{
    sourceForest = source;
    targetForest = target;
    targetType = OpndType::FOREST;
    caches.resize(1);
#ifdef BRAVE_DD_CONCRETIZATION_HELP_CACHE
    if (opType == UnaryOperationType::UOP_CONCRETIZE_OSM) {
        caches.resize(2);
    } else if (opType == UnaryOperationType::UOP_CONCRETIZE_TSM) {
        caches.resize(3);
    }
#endif
}
UnaryOperation::UnaryOperation(UnaryOperationType type, Forest* source, OpndType target)
:opType(type)
{
    sourceForest = source;
    targetForest = source;
    targetType = target;
    caches.resize(1);
}
UnaryOperation::~UnaryOperation()
{
    caches.clear();
    sourceForest = nullptr;
    targetForest = nullptr;
}

void UnaryOperation::sweepAndEnlarge(const size_t cacheID)
{
    // first check if number of entries reach to the thresholds
    double ratio = static_cast<double>(caches[cacheID].numEntries) / caches[cacheID].size;
    // it's time to sweep? TBD
    // it's time to enlarge?
    if ((ratio > thresholdsEnlarge) && (caches[0].size < (uint64_t)0x01 << 62)) {
        caches[0].size *= 2;
        caches[0].enlarge(caches[0].size);
    }
}

void UnaryOperation::compute(const Func& source, Func& target)
{
    if (!checkForestCompatibility()) {
        throw error(ErrCode::INVALID_OPERATION, __FILE__, __LINE__);
    }
    Level numVars = sourceForest->getSetting().getNumVars();
    Edge ans;
    // copy to target forest
    ans = computeCOPY(numVars, source.getEdge());
    if (opType == UnaryOperationType::UOP_COPY) {
        target.setEdge(ans);
        return;
    } else if (opType == UnaryOperationType::UOP_COMPLEMENT) {
        // target forest allows complement flag
        if ((targetForest->getSetting().getCompType() != NO_COMP)
            && (targetForest->getSetting().getEncodeMechanism() == TERMINAL)) {
            ans.complement();
            // normalize edge
            if (!targetForest->getSetting().hasReductionRule(ans.getRule())) {
                ans = targetForest->normalizeEdge(numVars, ans);
            }
            target.setEdge(ans);
            return;
        }
        // here is the forest that does not allow complement bit, recursively compute
        ans = computeCOMPLEMENT(numVars, ans);
    } else {
        // TBD
    }
    target.setEdge(ans);
    // other info TBD
}

void UnaryOperation::compute(const Func& source, long& target)
{
    if (!checkForestCompatibility()) {
        throw error(ErrCode::INVALID_OPERATION, __FILE__, __LINE__);
    }
    Level numVars = sourceForest->getSetting().getNumVars();
    if (opType == UnaryOperationType::UOP_CARDINALITY) {
        target = computeCARD(numVars, source.getEdge());
    }
    // TBD
}

void UnaryOperation::compute(const Func& source, double& target)
{
    if (!checkForestCompatibility()) {
        throw error(ErrCode::INVALID_OPERATION, __FILE__, __LINE__);
    }
    // TBD
}

void UnaryOperation::compute(const Func& source, const Func& dc, Func& target)
{
    if (!checkForestCompatibility()) {
        throw error(ErrCode::INVALID_OPERATION, __FILE__, __LINE__);
    }
    Level numVars = sourceForest->getSetting().getNumVars();
    Edge ans;
    // copy to target forest
    ans = computeCOPY(numVars, source.getEdge());
    if (opType == UnaryOperationType::UOP_CONCRETIZE_RST) {
        ans = computeRST(numVars, ans, dc.getEdge());
    } else if (opType == UnaryOperationType::UOP_CONCRETIZE_OSM) {
        ans = computeOSM(numVars, ans, dc.getEdge());
    } else if (opType == UnaryOperationType::UOP_CONCRETIZE_TSM) {
        ans = computeTSM(numVars, ans, dc.getEdge());
    } 
    target.setEdge(ans);
}

void UnaryOperation::compute(const Func& source, const Value& val, Func& target)
{
    if (!checkForestCompatibility()) {
        throw error(ErrCode::INVALID_OPERATION, __FILE__, __LINE__);
    }
    Level numVars = sourceForest->getSetting().getNumVars();
    Edge ans;
    // copy to target forest
    ans = computeCOPY(numVars, source.getEdge());
    if (opType == UnaryOperationType::UOP_CONCRETIZE_RST) {
        ans = computeRST(numVars, ans, val);
    } else if (opType == UnaryOperationType::UOP_CONCRETIZE_OSM) {
        ans = computeOSM(numVars, ans, val);
    } else if (opType == UnaryOperationType::UOP_CONCRETIZE_TSM) {
        ans = computeTSM(numVars, ans, val);
    }
    target.setEdge(ans);
}

bool UnaryOperation::checkForestCompatibility() const
{
    bool ans = 1;
    // TBD
    return ans;
}

Edge UnaryOperation::computeCOPY(const Level lvl, const Edge& source)
{
    // Direct return if the target forest is the source forest
    if (sourceForest == targetForest) {
        return source;
    }
    // Terminal case
    if (source.getNodeLevel() == 0) {
        // same encoding mechanism or special value
        if ((sourceForest->getSetting().getEncodeMechanism() == targetForest->getSetting().getEncodeMechanism())
            || isTerminalSpecial(source.getEdgeHandle())) {
            return targetForest->normalizeEdge(lvl, source);
        } else if ((targetForest->getSetting().getEncodeMechanism() == EDGE_PLUS)
                    || (targetForest->getSetting().getEncodeMechanism() == EDGE_PLUSMOD)    // be carefull, TBD
                    || (targetForest->getSetting().getEncodeMechanism() == EDGE_MULT)) {
            // terminal-encoding to edge-valued encoding
            Edge ans;
            EdgeHandle constant = makeTerminal(SpecialValue::OMEGA);
            packRule(constant, source.getRule());
            ans.setEdgeHandle(constant);
            ans.setValue(getTerminalValue(source.getEdgeHandle()));
            return targetForest->normalizeEdge(lvl, ans);
        } else {
            // edge-valued encoding to terminal-encoding
            Edge ans;
            EdgeHandle constant = 0;
            if (source.isConstantOmega()) {
                constant = makeTerminal(source.getValue());
                packRule(constant, source.getRule());
                ans.setEdgeHandle(constant);
                return targetForest->normalizeEdge(lvl, ans);
            } else {
                constant = source.getEdgeHandle();
                ans.setEdgeHandle(constant);
                return ans;
            }
        }
    }
    // the answer
    Edge ans;
    // check compute table
    Edge cacheEdge = source;
    if (caches[0].check(lvl, source, ans)) return ans;
    std::vector<Edge> childEdges;
    if (targetForest->getSetting().isRelation()) {
        childEdges = std::vector<Edge>(4);
    } else {
        childEdges = std::vector<Edge>(2);
    }
    for (size_t i=0; i<childEdges.size(); i++) {
        childEdges[i] = sourceForest->cofact(lvl, source, i);
        childEdges[i] = computeCOPY(lvl-1, childEdges[i]);
    }
    // reduce
    EdgeLabel label = 0;
    packRule(label, RULE_X);
    ans = targetForest->reduceEdge(lvl, label, lvl, childEdges);
    // cache
    cacheAdd(0, lvl, source, ans);

    return ans;
}

Edge UnaryOperation::computeCOMPLEMENT(const Level lvl, const Edge& source)
{
    /* Assuming this is within the same target forest
     Here is forest that does not allow complement bit */
    
    Edge ans;    
    // terminal case
    if (source.getNodeLevel() == 0) {
        ans = source;
        ans.complement();
        return targetForest->normalizeEdge(lvl, ans);
    } else {
        Edge cacheEdge = source;
        // check cache
        if (caches[0].check(lvl, source, ans)) return ans;
        // protect edge for sweep
        // ProtectEdge protectSource(targetForest, cacheEdge);
        std::vector<Edge> childEdges;
        if (targetForest->getSetting().isRelation()) {
            childEdges = std::vector<Edge>(4);
        } else {
            childEdges = std::vector<Edge>(2);
        }
        for (size_t i=0; i<childEdges.size(); i++) {
            childEdges[i] = targetForest->cofact(source.getNodeLevel(), source, i);
            childEdges[i] = computeCOMPLEMENT(source.getNodeLevel()-1, childEdges[i]);
        }
        EdgeLabel label = 0;
        packRule(label, compRule(source.getRule()));
        ans = targetForest->reduceEdge(lvl, label, source.getNodeLevel(), childEdges);
        // cache
        cacheAdd(0, lvl, source, ans);
    }
    return ans;
}

long UnaryOperation::computeCARD(const Level lvl, const Edge& source)
{
    // base cases:
    if (lvl == 0) {
        if (targetForest->getSetting().getEncodeMechanism() == TERMINAL) {
            if (targetForest->setting.hasNegInf() || targetForest->setting.hasPosInf() || targetForest->setting.hasUnDef()) {
                if (!isTerminalSpecial(source.getEdgeHandle())) return 1;
            } else {
                return source.getComp() ^ isTerminalOne(source.getEdgeHandle());
            }
            // other value TBD
        } else {
            if (targetForest->setting.hasNegInf() || targetForest->setting.hasPosInf() || targetForest->setting.hasUnDef()) {
                if (isTerminalSpecial(SpecialValue::OMEGA, source.getEdgeHandle())) return 1;
            } else {
                if (isTerminalSpecial(SpecialValue::OMEGA, source.getEdgeHandle())
                    && (source.getValue() == Value(1))) { // other value TBD
                    return 1;
                }
            }
        }
    }
    if (source.getNodeLevel() == 0) {
        if (targetForest->getSetting().getEncodeMechanism() == TERMINAL) {
            if (targetForest->setting.hasNegInf() || targetForest->setting.hasPosInf() || targetForest->setting.hasUnDef()) {
                // count path to non-special
                if (!isTerminalSpecial(source.getEdgeHandle())) return (targetForest->getSetting().isRelation()) ? (0x01 << (2*lvl)) : (0x01 << lvl);
                else return 0;
            } else {
                // count path to 1
                if (source.isConstantZero()) {
                    return 0;
                } else if (source.isConstantOne()) {
                    return (targetForest->getSetting().isRelation()) ? (0x01 << (2*lvl)) : (0x01 << lvl);
                } else if ((source.getRule() == RULE_EL1) || (source.getRule() == RULE_EH1)
                            || (source.getRule() == RULE_AH0) || (source.getRule() == RULE_AL0)) {
                    return (0x01 << lvl) - 1;
                } else if ((source.getRule() == RULE_EL0) || (source.getRule() == RULE_EH0)
                            || (source.getRule() == RULE_AH1) || (source.getRule() == RULE_AL1)) {
                    return 1;
                } else if (source.getRule() == RULE_I0) {
                    return 0x01 << lvl;
                } else if (source.getRule() == RULE_I1) {
                    return (0x01 << (2*lvl)) - (0x01 << lvl);
                }
            }
        } else {
            if (targetForest->setting.hasNegInf() || targetForest->setting.hasPosInf() || targetForest->setting.hasUnDef()) {
                if (isTerminalSpecial(SpecialValue::OMEGA, source.getEdgeHandle())) return (targetForest->getSetting().isRelation()) ? (0x01 << (2*lvl)) : (0x01 << lvl);
                else return 0;
            } else {
                if (isTerminalSpecial(SpecialValue::OMEGA, source.getEdgeHandle())
                    && (source.getValue() == Value(1))) {
                    return (targetForest->getSetting().isRelation()) ? (0x01 << (2*lvl)) : (0x01 << lvl);
                } else {
                    return 0;
                }
            }
        }
    }
    // check the result of the target node
    Edge cacheEdge = source;
    cacheEdge.setRule(RULE_X);
    long num = 0;
    // protect edge for sweep
    // ProtectEdge protectSource(targetForest, cacheEdge);
    if (!caches[0].check(source.getNodeLevel(), cacheEdge, num)) {
        // compute recursively
        std::vector<Edge> child;
        if (targetForest->getSetting().isRelation()) {
            child = std::vector<Edge>(4);
        } else {
            child = std::vector<Edge>(2);
        }
        long newNum = 0;
        for (char i=0; i<(char)child.size(); i++) {
            child[i] = targetForest->cofact(source.getNodeLevel(), source, i);
            newNum += computeCARD(source.getNodeLevel()-1, child[i]);
        }
        num = newNum;
        // save to the cache
        cacheAdd(0, source.getNodeLevel(), cacheEdge, newNum);
    }
    // consider the incoming edge rule
    int multiplier = 1;
    int adder = 0;
    if (source.getRule() == RULE_X) {
        multiplier = (targetForest->getSetting().isRelation()) ? (0x01 << (2*(lvl-source.getNodeLevel()))) : (0x01 << (lvl-source.getNodeLevel()));
    } else if ((source.getRule() == RULE_EL1) || (source.getRule() == RULE_EH1)) {
        adder = (0x01 << lvl) - (0x01 << source.getNodeLevel());
    } else if ((source.getRule() == RULE_AL0) || (source.getRule() == RULE_AH0)) {
        multiplier = (0x01 << (lvl - source.getNodeLevel())) - 1;
    } else if ((source.getRule() == RULE_AL1) || (source.getRule() == RULE_AH1)) {
        multiplier = (0x01 << (lvl - source.getNodeLevel())) - 1;
        adder = 0x01 << source.getNodeLevel();
    } else if (source.getRule() == RULE_I0) {
        multiplier = 0x01 << (lvl - source.getNodeLevel());
    } else if (source.getRule() == RULE_I1) {
        multiplier = 0x01 << (lvl - source.getNodeLevel());
        adder = (0x01 << (2*(lvl-source.getNodeLevel()))) - (0x01 << (lvl-source.getNodeLevel()));
    }
    return multiplier * num + adder;
}

Edge UnaryOperation::computeRST(const Level lvl, const Edge& source, const Edge& dc)
{
    // terminal case
    if (source.getNodeLevel() == 0) return source;
    // check cache
    Edge result;
    if (caches[0].check(lvl, source, dc, result)) return result;
    // check child edge
    Level level = MAX(source.getNodeLevel(), dc.getNodeLevel());
    Edge lc = targetForest->cofact(level, source, 0);
    Edge hc = targetForest->cofact(level, source, 1);
    Edge lc_dc = targetForest->cofact(level, dc, 0);
    Edge hc_dc = targetForest->cofact(level, dc, 1);
    if (lc_dc.isConstantOne()) {
        return computeRST(level-1, hc, hc_dc);
    } else if (hc_dc.isConstantOne()) {
        return computeRST(level-1, lc, lc_dc);
    }
    // recursively compute
    std::vector<Edge> child(2);
    child[0] = computeRST(level-1, lc, lc_dc);
    child[1] = computeRST(level-1, hc, hc_dc);
    // reduce edge
    EdgeLabel root = 0;
    packRule(root, RULE_X);
    result = targetForest->reduceEdge(lvl, root, level, child);
    // add to cache
    cacheAdd(0, lvl, source, result);
    return result;
}

Edge UnaryOperation::computeRST(const Level lvl, const Edge& source, const Value& val)
{
    // terminal case
    if (isTerminal(source.getEdgeHandle())) return source;
    // check cache
    Edge result;
    if (caches[0].check(lvl, source, result)) return result;
    // check child edge
    Level level = source.getNodeLevel();
    Edge lc = targetForest->cofact(level, source, 0);
    Edge hc = targetForest->cofact(level, source, 1);
    if (isTerminal(lc.getEdgeHandle())) {
        Value lv = getTerminalValue(lc.getEdgeHandle());
        if (val.getType() == VOID) {
            if (lv == val) return computeRST(level-1, hc, val);
        } else {
            if (val == ((targetForest->getSetting().getEncodeMechanism() == TERMINAL) ? lv : lc.getValue())) return computeRST(level-1, hc, val);
        }
    }
    if (isTerminal(hc.getEdgeHandle())) {
        Value hv = getTerminalValue(hc.getEdgeHandle());
        if (val.getType() == VOID) {
            if (val == hv) return computeRST(level-1, lc, val);
        } else {
            if (val == ((targetForest->getSetting().getEncodeMechanism() == TERMINAL) ? hv : hc.getValue())) return computeRST(level-1, lc, val);
        }
    }
    // recursively compute
    std::vector<Edge> child(2);
    child[0] = computeRST(level-1, lc, val);
    child[1] = computeRST(level-1, hc, val);
    // reduce edge
    EdgeLabel root = 0;
    packRule(root, RULE_X);
    result = targetForest->reduceEdge(lvl, root, level, child);
    // add to cache
    cacheAdd(0, lvl, source, result);
    return result;
}

Edge UnaryOperation::computeOSM(const Level lvl, const Edge& source, const Edge& dc)
{
    // terminal case
    if (source.getNodeLevel() == 0) return source;
    // check cache
    Edge result;
    if (caches[0].check(lvl, source, dc, result)) return result;
    // check child edge
    Level level = MAX(source.getNodeLevel(), dc.getNodeLevel());
    Edge lc = targetForest->cofact(level, source, 0);
    Edge hc = targetForest->cofact(level, source, 1);
    Edge lc_dc = targetForest->cofact(level, dc, 0);
    Edge hc_dc = targetForest->cofact(level, dc, 1);
    if (lc_dc.isConstantOne()) {
        return computeOSM(level-1, hc, hc_dc);
    } else if (hc_dc.isConstantOne()) {
        return computeOSM(level-1, lc, lc_dc);
    }
    // compare child edges
    unsigned comp = compareOSM(lc, hc, lc_dc, hc_dc);
    if (comp == '<') {
        return computeOSM(level-1, lc, lc_dc);
    }
    if (comp == '>') {
        return computeOSM(level-1, hc, hc_dc);
    }
    // new node
    std::vector<Edge> child(2);
    child[0] = computeOSM(level-1, lc, lc_dc);
    child[1] = computeOSM(level-1, hc, hc_dc);
    // reduce edge
    EdgeLabel root = 0;
    packRule(root, RULE_X);
    result = targetForest->reduceEdge(lvl, root, level, child);
    // add cache
    cacheAdd(0, lvl, source, dc, result);
    return result;
}

Edge UnaryOperation::computeOSM(const Level lvl, const Edge& source, const Value& val)
{
    // terminal case
    if ((source.getNodeLevel() == 0)) return source;
    // check cache
    Edge result;
    if (caches[0].check(lvl, source, result)) return result;
    // check child edge
    Level level = source.getNodeLevel();
    Edge lc = targetForest->cofact(level, source, 0);
    Edge hc = targetForest->cofact(level, source, 1);
    // compare child edges
    unsigned comp = compareOSM(lc, hc, val);
    if (comp == '<') {
        return computeOSM(level-1, lc, val);
    }
    if (comp == '>') {
        return computeOSM(level-1, hc, val);
    }
    // new node
    std::vector<Edge> child(2);
    child[0] = computeOSM(level-1, lc, val);
    child[1] = computeOSM(level-1, hc, val);
    // reduce edge
    EdgeLabel root = 0;
    packRule(root, RULE_X);
    result = targetForest->reduceEdge(lvl, root, level, child);
    // add cache
    cacheAdd(0, lvl, source, result);
    return result;
}

Edge UnaryOperation::computeTSM(const Level lvl, const Edge& source, const Edge& dc)
{
    // terminal case
    if (source.getNodeLevel() == 0) return source;
    // check cache
    Edge result;
    if (caches[0].check(lvl, source, result)) return result;
    // check child edge
    Level level = MAX(source.getNodeLevel(), dc.getNodeLevel());
    Edge lc = targetForest->cofact(level, source, 0);
    Edge hc = targetForest->cofact(level, source, 1);
    Edge lc_dc = targetForest->cofact(level, dc, 0);
    Edge hc_dc = targetForest->cofact(level, dc, 1);
    if (lc_dc.isConstantOne()) {
        return computeTSM(lvl, hc, hc_dc);
    } else if (hc_dc.isConstantOne()) {
        return computeTSM(lvl, lc, lc_dc);
    }
    // check child edges
    if (hasCommonTSM(lc, hc, lc_dc, hc_dc)) {
        Edge child_common = commonTSM(level-1, lc, hc, lc_dc, hc_dc);
        if (level > source.getNodeLevel()) {
            // new dc is lc_dc & hc_dc !!!
            BinaryOperationType type = BinaryOperationType::BOP_INTERSECTION;
            BinaryOperation* bo = BOPs.find(type, targetForest, targetForest, targetForest);
            if (!bo) {
                bo = BOPs.add(new BinaryOperation(type, targetForest, targetForest, targetForest));
            }
            return computeTSM(level-1, child_common, bo->computeElmtWise(level-1, lc_dc, hc_dc));
        }
        return computeTSM(lvl, child_common, dc);
    }
    // new node
    std::vector<Edge> child(2);
    child[0] = computeTSM(level-1, lc, lc_dc);
    child[1] = computeTSM(level-1, hc, hc_dc);
    // reduce edge
    EdgeLabel root = 0;
    packRule(root, RULE_X);
    result = targetForest->reduceEdge(lvl, root, level, child);
    // add cache
    cacheAdd(0, lvl, source, dc, result);
    return result;
}

Edge UnaryOperation::computeTSM(const Level lvl, const Edge& source, const Value& val)
{
    // terminal case
    if (source.getNodeLevel() == 0) return source;
    // check cache
    Edge result;
    if (caches[0].check(lvl, source, result)) return result;
    // check child edge
    Level level = source.getNodeLevel();
    Edge lc = targetForest->cofact(level, source, 0);
    Edge hc = targetForest->cofact(level, source, 1);
    if (isTerminal(lc.getEdgeHandle())) {
        Value lv = getTerminalValue(lc.getEdgeHandle());
        if (val.getType() == VOID) {
            if (lv == val) return computeTSM(level-1, hc, val);
        } else {
            if (val == ((targetForest->getSetting().getEncodeMechanism() == TERMINAL) ? lv : lc.getValue())) return computeTSM(level-1, hc, val);
        }
    }
    if (isTerminal(hc.getEdgeHandle())) {
        Value hv = getTerminalValue(hc.getEdgeHandle());
        if (val.getType() == VOID) {
            if (val == hv) return computeTSM(level-1, lc, val);
        } else {
            if (val == ((targetForest->getSetting().getEncodeMechanism() == TERMINAL) ? hv : hc.getValue())) return computeTSM(level-1, lc, val);
        }
    }
    if (hasCommonTSM(lc, hc, val)) {
        Edge child_common = commonTSM(level-1, lc, hc, val);
        return computeTSM(lvl, child_common, val);
    }
    // new node
    std::vector<Edge> child(2);
    child[0] = computeTSM(level-1, lc, val);
    child[1] = computeTSM(level-1, hc, val);
    // reduce edge
    EdgeLabel root = 0;
    packRule(root, RULE_X);
    result = targetForest->reduceEdge(lvl, root, level, child);
    // add cache
    cacheAdd(0, lvl, source, result);
    return result;
}

char UnaryOperation::compareOSM(const Edge& source1, const Edge& source2, const Edge& d1, const Edge& d2)
{
    // terminal cases
    if (d1.isConstantOne()) {return '>';}
    if (d2.isConstantOne()) {return '<';}
    if ((source1 == source2) && (d1.isConstantZero() && d2.isConstantZero())) {return '=';}
    if ((source1.getNodeLevel() == source2.getNodeLevel()) && (source1.getNodeLevel() == 0) && (d1.isConstantZero() && d2.isConstantZero())) {return '!';}   // both different terminal value and not dc
    // copy for swap if needed
    Edge e1 = source1;
    Edge e2 = source2;
    Edge dc1 = d1;
    Edge dc2 = d2;
    // the highest level
    Level highest = MAX(MAX(e1.getNodeLevel(), e2.getNodeLevel()), MAX(dc1.getNodeLevel(), dc2.getNodeLevel()));
    char ans;
#ifdef BRAVE_DD_CONCRETIZATION_HELP_CACHE
    // check cache
    bool isSwap = 0;
    if (e1.getEdgeHandle() > e2.getEdgeHandle()) {
        SWAP(e1, e2);
        SWAP(dc1, dc2);
        isSwap = 1;
    }
    if (caches[1].check(highest, e1, e2, dc1, dc2, ans)) {
        if (isSwap) {
            if (ans == '<') ans = '>';
            if (ans == '>') ans = '<';
        }
        return ans;
    }
#endif
    // recursively compare
    char comp0, comp1;
    comp0 = compareOSM(targetForest->cofact(highest, e1, 0),
                        targetForest->cofact(highest, e2, 0),
                        targetForest->cofact(highest, dc1, 0),
                        targetForest->cofact(highest, dc2, 0));
    comp1 = compareOSM(targetForest->cofact(highest, e1, 1),
                        targetForest->cofact(highest, e2, 1),
                        targetForest->cofact(highest, dc1, 1),
                        targetForest->cofact(highest, dc2, 1));
    if ((comp0 == '=') || (comp0 == comp1)) {
        ans = comp1;
    } else if (comp1 == '=') {
        ans = comp0;
    } else {
        ans = '!';
    }
#ifdef BRAVE_DD_CONCRETIZATION_HELP_CACHE
    // for swap
    if (isSwap) {
        if (ans == '<') ans = '>';
        else if (ans == '>') ans = '<';
    }
    // add cache
    cacheAdd(1, highest, e1, e2, dc1, dc2, ans);
#endif
    return ans;
}

char UnaryOperation::compareOSM(const Edge& source1, const Edge& source2, const Value& val)
{
    // terminal cases
    if (isTerminal(source1.getEdgeHandle())) {
        Value v = getTerminalValue(source1.getEdgeHandle());
        if (val.getType() == VOID) {
            if (val == v) return '>';
        } else {
            if (val == ((targetForest->getSetting().getEncodeMechanism() == TERMINAL) ? v : source1.getValue())) return '>';
        }
    }
    if (isTerminal(source2.getEdgeHandle())) {
        Value v = getTerminalValue(source2.getEdgeHandle());
        if (val.getType() == VOID) {
            if (val == v) return '<';
        } else {
            if (val == ((targetForest->getSetting().getEncodeMechanism() == TERMINAL) ? v : source2.getValue())) return '<';
        }
    }
    if (source1 == source2) {return '=';}
    if ((source1.getNodeLevel() == source2.getNodeLevel()) && (source1.getNodeLevel() == 0)) {return '!';}   // both different terminal value and not dc
    // copy for swap if needed
    Edge e1 = source1;
    Edge e2 = source2;
    // the highest level
    Level highest = MAX(e1.getNodeLevel(), e2.getNodeLevel());
    char ans;
#ifdef BRAVE_DD_CONCRETIZATION_HELP_CACHE
    //check cache
    bool isSwap = 0;
    if (e1.getEdgeHandle() > e2.getEdgeHandle()) {
        SWAP(e1, e2);
        isSwap = 1;
    }
    if (caches[1].check(highest, e1, e2, ans)) {
        if (isSwap) {
            if (ans == '<') ans = '>';
            if (ans == '>') ans = '<';
        }
        return ans;
    }
#endif
    // recursively compare
    char comp0, comp1;
    comp0 = compareOSM(targetForest->cofact(highest, e1, 0),
                        targetForest->cofact(highest, e2, 0),
                        val);
    comp1 = compareOSM(targetForest->cofact(highest, e1, 1),
                        targetForest->cofact(highest, e2, 1),
                        val);
    
    if ((comp0 == '=') || (comp0 == comp1)) {
        ans = comp1;
    } else if (comp1 == '=') {
        ans = comp0;
    } else {
        ans = '!';
    }
#ifdef BRAVE_DD_CONCRETIZATION_HELP_CACHE
    if (isSwap) {
        if (ans == '<') ans = '>';
        else if (ans == '>') ans = '<';
    }
    // add cache
    cacheAdd(1, highest, e1, e2, ans);
#endif
    return ans;
}

bool UnaryOperation::hasCommonTSM(const Edge& source1, const Edge& source2, const Edge& d1, const Edge& d2)
{
    // terminal cases
    if (d1.isConstantOne()) {return true;}
    if (d2.isConstantOne()) {return true;}
    if (source1 == source2) {return true;}
    if ((source1.getNodeLevel() == source2.getNodeLevel()) && (source1.getNodeLevel() == 0)) {return false;}   // both different terminal value and not dc
    // copy for swap if needed
    Edge e1 = source1;
    Edge e2 = source2;
    Edge dc1 = d1;
    Edge dc2 = d2;
    // the highest level
    Level highest = MAX(MAX(e1.getNodeLevel(), e2.getNodeLevel()), MAX(dc1.getNodeLevel(), dc2.getNodeLevel()));
    bool ans = 0;
#ifdef BRAVE_DD_CONCRETIZATION_HELP_CACHE
    // check cache
    if (e1.getEdgeHandle() > e2.getEdgeHandle()) {
        SWAP(e1, e2);
        SWAP(dc1, dc2);
    }
    if (caches[1].check(highest, e1, e2, dc1, dc2, ans)) return ans;
#endif
    // recursively check
    bool cmp0, cmp1;
    cmp0 = hasCommonTSM(targetForest->cofact(highest, e1, 0),
                        targetForest->cofact(highest, e2, 0),
                        targetForest->cofact(highest, dc1, 0),
                        targetForest->cofact(highest, dc2, 0));
    cmp1 = hasCommonTSM(targetForest->cofact(highest, e1, 1),
                        targetForest->cofact(highest, e2, 1),
                        targetForest->cofact(highest, dc1, 1),
                        targetForest->cofact(highest, dc2, 1));
    ans = (cmp0 && cmp1);
#ifdef BRAVE_DD_CONCRETIZATION_HELP_CACHE
    // add cache
    cacheAdd(1, highest, e1, e2, dc1, dc2, ans);
#endif
    return ans;
}

bool UnaryOperation::hasCommonTSM(const Edge& source1, const Edge& source2, const Value& val)
{
    // terminal cases
    if (isTerminal(source1.getEdgeHandle())) {
        Value v = getTerminalValue(source1.getEdgeHandle());
        if (val.getType() == VOID) {
            if (val == v) return true;
        } else {
            if (val == ((targetForest->getSetting().getEncodeMechanism() == TERMINAL) ? v : source1.getValue())) return true;
        }
    }
    if (isTerminal(source2.getEdgeHandle())) {
        Value v = getTerminalValue(source2.getEdgeHandle());
        if (val.getType() == VOID) {
            if (val == v) return true;
        } else {
            if (val == ((targetForest->getSetting().getEncodeMechanism() == TERMINAL) ? v : source2.getValue())) return true;
        }
    }
    if (source1 == source2) {return true;}
    if ((source1.getNodeLevel() == source2.getNodeLevel()) && (source1.getNodeLevel() == 0)) {return false;}   // both different terminal value and not dc
    // copy for swap if needed
    Edge e1 = source1;
    Edge e2 = source2;
    // the highest level
    Level highest = MAX(source1.getNodeLevel(), source2.getNodeLevel());
    bool ans = 0;
#ifdef BRAVE_DD_CONCRETIZATION_HELP_CACHE
    // check cache
    if (e1.getEdgeHandle() > e2.getEdgeHandle()) SWAP(e1, e2);
    if (caches[1].check(highest, e1, e2, ans)) return ans;
#endif
    // recursively check
    bool cmp0, cmp1;
    cmp0 = hasCommonTSM(targetForest->cofact(highest, e1, 0),
                        targetForest->cofact(highest, e2, 0),
                        val);
    cmp1 = hasCommonTSM(targetForest->cofact(highest, e1, 1),
                        targetForest->cofact(highest, e2, 1),
                        val);
    ans = (cmp0 && cmp1);
#ifdef BRAVE_DD_CONCRETIZATION_HELP_CACHE
    // add cache
    cacheAdd(1, highest, e1, e2, ans);
#endif
    return ans;
}

Edge UnaryOperation::commonTSM(const Level lvl, const Edge& source1, const Edge& source2, const Edge& d1, const Edge& d2)
{
    // terminal cases
    if (d1.isConstantOne()) {return source2;}
    if (d2.isConstantOne()) {return source1;}
    if (source1 == source2) {return source1;}
    // copy for swap if needed
    Edge e1 = source1;
    Edge e2 = source2;
    Edge dc1 = d1;
    Edge dc2 = d2;
    // the highest level
    Level highest = MAX(MAX(e1.getNodeLevel(), e2.getNodeLevel()), MAX(dc1.getNodeLevel(), dc2.getNodeLevel()));
    Edge result;
#ifdef BRAVE_DD_CONCRETIZATION_HELP_CACHE
    // check cache
    if (e1.getEdgeHandle() > e2.getEdgeHandle()) {
        SWAP(e1, e2);
        SWAP(dc1, dc2);
    }
    if (caches[2].check(highest, e1, e2, dc1, dc2, result)) return result;
#endif
    // recursively computing
    std::vector<Edge> child(2);
    child[0] = commonTSM(highest - 1,
                        targetForest->cofact(highest, e1, 0),
                        targetForest->cofact(highest, e2, 0),
                        targetForest->cofact(highest, dc1, 0),
                        targetForest->cofact(highest, dc2, 0));
    child[1] = commonTSM(highest - 1,
                        targetForest->cofact(highest, e1, 1),
                        targetForest->cofact(highest, e2, 1),
                        targetForest->cofact(highest, dc1, 1),
                        targetForest->cofact(highest, dc2, 1));
    // reduce edge
    EdgeLabel root = 0;
    packRule(root, RULE_X);
    result = targetForest->reduceEdge(lvl, root, highest, child);
#ifdef BRAVE_DD_CONCRETIZATION_HELP_CACHE
    // add cache
    cacheAdd(2, highest, e1, e2, dc1, dc2, result);
#endif
    return result;
}

Edge UnaryOperation::commonTSM(const Level lvl, const Edge& source1, const Edge& source2, const Value& val)
{
    // terminal cases
    if (isTerminal(source1.getEdgeHandle())) {
        Value v = getTerminalValue(source1.getEdgeHandle());
        if (val.getType() == VOID) {
            if (val == v) return source2;
        } else {
            if (val == ((targetForest->getSetting().getEncodeMechanism() == TERMINAL) ? v : source1.getValue())) return source2;
        }
    }
    if (isTerminal(source2.getEdgeHandle())) {
        Value v = getTerminalValue(source2.getEdgeHandle());
        if (val.getType() == VOID) {
            if (val == v) return source1;
        } else {
            if (val == ((targetForest->getSetting().getEncodeMechanism() == TERMINAL) ? v : source2.getValue())) return source1;
        }
    }
    if (source1 == source2) {return source1;}
    // copy for swap if needed
    Edge e1 = source1;
    Edge e2 = source2;
    // the highest level
    Level highest = MAX(source1.getNodeLevel(), source2.getNodeLevel());
    Edge result;
#ifdef BRAVE_DD_CONCRETIZATION_HELP_CACHE
    //check cache
    if (e1.getEdgeHandle() > e2.getEdgeHandle()) {
        SWAP(e1, e2);
    }
    if (caches[2].check(highest, e1, e2, result)) return result;
#endif
    // recursively computing
    std::vector<Edge> child(2);
    child[0] = commonTSM(highest - 1,
                        targetForest->cofact(highest, e1, 0),
                        targetForest->cofact(highest, e2, 0),
                        val);
    child[1] = commonTSM(highest - 1,
                        targetForest->cofact(highest, e1, 1),
                        targetForest->cofact(highest, e2, 1),
                        val);
    // reduce edge
    EdgeLabel root = 0;
    packRule(root, RULE_X);
    result = targetForest->reduceEdge(lvl, root, highest, child);
#ifdef BRAVE_DD_CONCRETIZATION_HELP_CACHE
    // add cache
    cacheAdd(2, highest, e1, e2, result);
#endif
    return result;
}

// ******************************************************************
// *                                                                *
// *                       UnaryList  methods                       *
// *                                                                *
// ******************************************************************
UnaryList::UnaryList(const std::string n)
{
    reset(n);
}

UnaryOperation* UnaryList::mtfUnary(const UnaryOperationType opT, const Forest* sourceF, const Forest* targetF)
{
    UnaryOperation* prev = front;
    UnaryOperation* curr = front->next;
    while (curr) {
        if ((curr->opType == opT) && (curr->sourceForest == sourceF) && (curr->targetForest == targetF)) {
            // Move to front
            prev->next = curr->next;
            curr->next = front;
            front = curr;
            return curr;
        }
        prev = curr;
        curr = curr->next;
    }
    return nullptr;
}

UnaryOperation* UnaryList::mtfUnary(const UnaryOperationType opT, const Forest* sourceF, const OpndType targetT)
{
    UnaryOperation* prev = front;
    UnaryOperation* curr = front->next;
    while (curr) {
        if ((curr->opType == opT) && (curr->sourceForest == sourceF) && (curr->targetType == targetT)) {
            // Move to front
            prev->next = curr->next;
            curr->next = front;
            front = curr;
            return curr;
        }
        prev = curr;
        curr = curr->next;
    }
    return nullptr;
}

void UnaryList::searchRemove(UnaryOperation* uop)
{
    if (!front || !uop) return;
    UnaryOperation* prev = front;
    UnaryOperation* curr = front->next;
    while (curr) {
        if (curr == uop) {
            prev->next = curr->next;
            delete curr;
            return;
        }
        prev = curr;
        curr = curr->next;
    }
}

void UnaryList::searchRemove(Forest* forest)
{
    if (!front || !forest) return;
    // check front first
    while (front && ((front->sourceForest == forest) || (front->targetForest == forest))) {
        UnaryOperation* toRemove = front;
        front = front->next;
        delete toRemove;
    }
    // check the remaining
    UnaryOperation* curr = front;
    while (curr && curr->next) {
        if ((curr->next->sourceForest == forest) || (curr->next->targetForest == forest)) {
            UnaryOperation* toRemove = curr->next;
            curr->next = curr->next->next;
            delete toRemove;
        } else {
            curr = curr->next;
        }
    }
}

void UnaryList::searchSweepCache(Forest* forest)
{
    if (!front || !forest) return;
    UnaryOperation* curr = front;
    bool isSource = curr->sourceForest == forest;
    bool isTarget = curr->targetForest == forest;
    while (curr) {
        if (isSource || isTarget) {
            // sweep cache
            // if opType is COPY, check if it's source or target forest
            if (curr->opType == UnaryOperationType::UOP_COPY) {
                curr->caches[0].sweep(forest, (isSource) ? 1 : 0);
            } else if (curr->opType == UnaryOperationType::UOP_COMPLEMENT) {
                if (isTarget) {
                    curr->caches[0].sweep(forest, 0);
                    curr->caches[0].sweep(forest, 1);
                }
            } else if (curr->opType == UnaryOperationType::UOP_CARDINALITY) {
                curr->caches[0].sweep(forest, 1);
            } else if (curr->opType == UnaryOperationType::UOP_CONCRETIZE_RST) {
                curr->caches[0].sweep(forest, 0);
                curr->caches[0].sweep(forest, 1);
            } else if (curr->opType == UnaryOperationType::UOP_CONCRETIZE_OSM) {
                curr->caches[0].sweep(forest, 0);
                curr->caches[0].sweep(forest, 1);
            } else if (curr->opType == UnaryOperationType::UOP_CONCRETIZE_TSM) {
                curr->caches[0].sweep(forest, 0);
                curr->caches[0].sweep(forest, 1);
            } else {
                // other operations, TBD
                std::cout << "other operation not implemented" << std::endl;
            }
        }
        curr = curr->next;
        if (curr) {
            isSource = curr->sourceForest == forest;
            isTarget = curr->targetForest == forest;
        }
    }
}

void UnaryList::reportCacheStat(std::ostream& out, int format) const
{
    UnaryOperation* curr = front;
    uint64_t n = 0;
    out << "UnaryList:\n";
    while (curr) {
        out << "CT " << n << "=============================\n";
        out << "Source Forest: " << curr->sourceForest->getSetting().getName() << "\n";
        out << "Result Forest: " << curr->targetForest->getSetting().getName() << "\n";
        out << "Operation Type: " << UOP2String(curr->opType) << "\n";
        out << "----------------------------------\n";
        curr->caches[0].reportStat(out, format);
        curr = curr->next;
        n++;
    }
}


// ******************************************************************
// *                                                                *
// *                                                                *
// *                 BinaryOperation  methods                       *
// *                                                                *
// *                                                                *
// ******************************************************************
BinaryOperation::BinaryOperation(BinaryOperationType type, Forest* source1, Forest* source2, Forest* res)
:opType(type)
{
    source1Forest = source1;
    source2Forest = source2;
    source2Type = OpndType::FOREST;
    resForest = res;
    caches.resize(1);
}
BinaryOperation::BinaryOperation(BinaryOperationType type, Forest* source1, OpndType source2, Forest* res)
:opType(type)
{
    source1Forest = source1;
    source2Forest = source1;
    source2Type = source2;
    resForest = res;
    caches.resize(1);
}
BinaryOperation::~BinaryOperation()
{
    caches.clear();
    source1Forest = nullptr;
    source2Forest = nullptr;
    resForest = nullptr;
}

void BinaryOperation::sweepAndEnlarge(const size_t cacheID)
{
    // first check if number of entries reach to the thresholds
    double ratio = static_cast<double>(caches[cacheID].numEntries) / caches[cacheID].size;
    // std::cout << "[sweep and enlarge] in " << BOP2String(this->opType) << "; ratio: " << ratio << std::endl;
    // ---------------------------------------------------------------------------------------------------------------
    // bool sweepDone = 0;
    // // it's time to sweep?
    // if ((ratio > thresholdsSweep)) {
    //     // mark all resgitered function and protected edges
    //     resForest->markAllFuncs();
    //     resForest->markAllProtectedEdges();
    //     // sweep
    //     resForest->markSweep();
    //     if ((opType == BinaryOperationType::BOP_PREIMAGE) || (opType == BinaryOperationType::BOP_POSTIMAGE)) {
    //         source1Forest->markAllFuncs();
    //         source1Forest->markAllProtectedEdges();
    //         source1Forest->markSweep();
    //     }
    //     sweepDone = 1;
    //     // update ratio
    //     ratio = static_cast<double>(caches[0].numEntries) / caches[0].size;
    // }
    // // it's time to enlarge?
    // if (sweepDone && (ratio > thresholdsEnlarge) && (caches[0].size < (uint64_t)0x01 << 62)) {
    // ---------------------------------------------------------------------------------------------------------------
    if ((ratio > thresholdsEnlarge) && (caches[cacheID].size < (uint64_t)0x01 << 62)) {
        caches[cacheID].size *= 2;
        caches[cacheID].enlarge(caches[cacheID].size);
    }
}

void BinaryOperation::compute(const Func& source1, const Func& source2, Func& res)
{
    if (!checkForestCompatibility()) {
        throw error(ErrCode::INVALID_OPERATION, __FILE__, __LINE__);
    }
    Edge ans;
    Func source1Equ;
    Func source2Equ;
    Level numVars = resForest->getSetting().getNumVars();
    // Unary operation to copy from source1 forest to target forest
    UnaryOperation* cp1 = UOPs.find(UnaryOperationType::UOP_COPY, source1.getForest(), res.getForest());
    if (!cp1) {
        cp1 = UOPs.add(new UnaryOperation(UnaryOperationType::UOP_COPY, source1.getForest(), res.getForest()));
    }
    // copy sources to the same target forest, if they are both set-of-states or relation
    if (source1Forest->getSetting().isRelation() == source2Forest->getSetting().isRelation()) {
        source1Equ = Func(res.getForest());
        cp1->compute(source1, source1Equ);
        source2Equ = Func(res.getForest());
        UnaryOperation* cp2 = UOPs.find(UnaryOperationType::UOP_COPY, source2.getForest(), res.getForest());
        if (!cp2) {
            cp2 = UOPs.add(new UnaryOperation(UnaryOperationType::UOP_COPY, source2.getForest(), res.getForest()));
        }
        cp2->compute(source2, source2Equ);
    }
    // compute the result
    if ((opType == BinaryOperationType::BOP_UNION)
        || (opType == BinaryOperationType::BOP_INTERSECTION)
        || (opType == BinaryOperationType::BOP_MINIMUM)
        || (opType == BinaryOperationType::BOP_MAXIMUM)
        || (opType == BinaryOperationType::BOP_PLUS)) { // more operations
        // Separate for efficiency? TBD
        ans = computeElmtWise(numVars, source1Equ.getEdge(), source2Equ.getEdge());
    } else if (opType == BinaryOperationType::BOP_PREIMAGE) {
        ans = computeImage(numVars, source1.getEdge(), source2.getEdge(), 1);
        Func ansEqu(source1.getForest(), ans);
        cp1->compute(ansEqu, res);
        return;
    } else if (opType == BinaryOperationType::BOP_POSTIMAGE) {
        ans = computeImage(numVars, source1.getEdge(), source2.getEdge());
        Func ansEqu(source1.getForest(), ans);
        cp1->compute(ansEqu, res);
        return;
    } else if (opType == BinaryOperationType::BOP_DIFFERENCE) {
        // temporary implementation
        UnaryOperation* comp = UOPs.find(UnaryOperationType::UOP_COMPLEMENT, source2Equ.getForest(), source2Equ.getForest());
        comp->compute(source2Equ, source2Equ);
        BinaryOperation* bop = BOPs.find(BinaryOperationType::BOP_INTERSECTION, source1Equ.getForest(), source1Equ.getForest(), source1Equ.getForest());
        bop->compute(source1Equ, source2Equ, source1Equ);
        ans = source1Equ.getEdge();
    } else {
        // TBD
        std::cerr << "[BraveDD] Warning: Operation \"" << BOP2String(opType) << "\" is not supported yet." << std::endl;
        std::cerr << "          This feature will be available soon in the next release." << std::endl;
        exit(1);
    }
    // passing result
    res.setEdge(ans);
    // caches[0].reportStat(std::cout);
}

void BinaryOperation::compute(const Func& source1, const ExplictFunc& source2, Func& res)
{
    // convert ExplictFunc to Func in source2Forest
    Func source2Func = source2.buildFunc(source2Forest);
    // call compute
    compute(source1, source2Func, res);
}

bool BinaryOperation::checkForestCompatibility() const
{
    bool ans = 1;
    // TBD
    return ans;
}

Edge BinaryOperation::computeElmtWise(const Level lvl, const Edge& source1, const Edge& source2)
{
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "compute elementwise(" << BOP2String(opType) << "): lvl: " << lvl << "; e1: ";
    source1.print(std::cout);
    std::cout << "; e2: ";
    source2.print(std::cout);
    std::cout << std::endl;
#endif
    // the final answer
    Edge ans;
    Edge e1, e2;
    // copy edge info
    e1 = resForest->normalizeEdge(lvl, source1);
    e2 = resForest->normalizeEdge(lvl, source2);
    /* =================================================================================================
    * Terminal cases based on operation types; This can be optimized by "template" class TBD
    * ================================================================================================*/
    /* -------------------------------------------------------------------------------------------------
    * Intersection and Union operations
    * ------------------------------------------------------------------------------------------------*/
    if ((opType == BinaryOperationType::BOP_INTERSECTION) || (opType == BinaryOperationType::BOP_UNION)) {
        /* Base case 1: two edges are the same */
    #ifdef BRAVE_DD_OPERATION_TRACE
        std::cout << "\tchecking base case 1\n";
    #endif
        if (e1 == e2) return e1;
        /* Base case 2: two edges are complemented */
    #ifdef BRAVE_DD_OPERATION_TRACE
        std::cout << "\tchecking base case 2\n";
    #endif
        if (e1.isComplementTo(e2)) {
            if (opType == BinaryOperationType::BOP_UNION) {
                EdgeHandle constant = makeTerminal(INT, 1);
                if (resForest->getSetting().getValType() == FLOAT) {
                    constant = makeTerminal(FLOAT, 1.0f);
                }
                packRule(constant, RULE_X);
                ans.setEdgeHandle(constant);
                ans = resForest->normalizeEdge(lvl, ans);
                return ans;
            } else {
                EdgeHandle constant = makeTerminal(INT, 0);
                if (resForest->getSetting().getValType() == FLOAT) {
                    constant = makeTerminal(FLOAT, 0.0f);
                }
                packRule(constant, RULE_X);
                ans.setEdgeHandle(constant);
                ans = resForest->normalizeEdge(lvl, ans);
                return ans;
            }
        }
        /* Base case 3: one edge is constant ONE edge */
    #ifdef BRAVE_DD_OPERATION_TRACE
        std::cout << "\tchecking base case 3\n";
    #endif
        if (e1.isConstantOne() || e2.isConstantOne()) {
            if (opType == BinaryOperationType::BOP_UNION) {
                EdgeHandle constant = makeTerminal(INT, 1);
                if (resForest->getSetting().getValType() == FLOAT) {
                    constant = makeTerminal(FLOAT, 1.0f);
                }
                packRule(constant, RULE_X);
                ans.setEdgeHandle(constant);
                ans = resForest->normalizeEdge(lvl, ans);
                return ans;
            } else if (opType == BinaryOperationType::BOP_INTERSECTION) {
                return (e1.isConstantOne()) ? e2 : e1;
            } else {
                // more operations, TBD
            }
        }
        /* Base case 4: one edge is constant ZERO edge */
    #ifdef BRAVE_DD_OPERATION_TRACE
        std::cout << "\tchecking base case 4\n";
    #endif
        if (e1.isConstantZero() || e2.isConstantZero()) {
            if (opType == BinaryOperationType::BOP_UNION) {
                return (e1.isConstantZero()) ? e2 : e1;
            } else if (opType == BinaryOperationType::BOP_INTERSECTION) {
                EdgeHandle constant = makeTerminal(INT, 0);
                if (resForest->getSetting().getValType() == FLOAT) {
                    constant = makeTerminal(FLOAT, 0.0f);
                }
                packRule(constant, RULE_X);
                ans.setEdgeHandle(constant);
                ans = resForest->normalizeEdge(lvl, ans);
                return ans;
            } else {
                // more operations, TBD
            }
        }
    /* -------------------------------------------------------------------------------------------------
    * Minimum and Maximum operations
    * ------------------------------------------------------------------------------------------------*/
    } else if ((opType == BinaryOperationType::BOP_MINIMUM) || (opType == BinaryOperationType::BOP_MAXIMUM)) {
        /* Base case 1: two edges are the same */
    #ifdef BRAVE_DD_OPERATION_TRACE
        std::cout << "\tchecking base case 1\n";
    #endif
        if (e1 == e2) return e1;
        /* Base case 2: one edge is constant*/
    #ifdef BRAVE_DD_OPERATION_TRACE
        std::cout << "\tchecking base case 2\n";
    #endif
        if (isTerminal(e1.getEdgeHandle())) {
            if (e1.isConstantPosInf()) {
                return (opType == BinaryOperationType::BOP_MINIMUM) ? e2 : e1;
            } else if (e1.isConstantNegInf()) {
                return (opType == BinaryOperationType::BOP_MINIMUM) ? e1 : e2;
            } else if (e1.isConstantOmega()) {
                // for EV
                if (e2.isConstantOmega()) {
                    if (e1.getValue() > e2.getValue()) {
                        return (opType == BinaryOperationType::BOP_MINIMUM) ? e2 : e1;
                    } else {
                        return (opType == BinaryOperationType::BOP_MINIMUM) ? e1 : e2;
                    }
                } else if (e2.isConstantPosInf()) {
                    return (opType == BinaryOperationType::BOP_MINIMUM) ? e1 : e2;
                } else if (e2.isConstantNegInf()) {
                    return (opType == BinaryOperationType::BOP_MINIMUM) ? e2 : e1;
                } else if (e2.isConstantUnDef()) {
                    // TBD for UnDef
                } else if (isTerminal(e2.getEdgeHandle())) {
                    // still a terminal value?
                    Value tv2 = getTerminalValue(e2.getEdgeHandle());
                    if (e1.getValue() > tv2) {
                        return (opType == BinaryOperationType::BOP_MINIMUM) ? e2 : e1;
                    } else {
                        return (opType == BinaryOperationType::BOP_MINIMUM) ? e1 : e2;
                    }
                }
            } else if (e1.isConstantUnDef()) {
                // TBD for UnDef
            } else if (isTerminal(e2.getEdgeHandle())) {
                // for MT
                Value tv1 = getTerminalValue(e1.getEdgeHandle());
                Value tv2 = getTerminalValue(e2.getEdgeHandle());
                // std::cout << "tv1: ";
                // tv1.print(std::cout);
                // std::cout << "; tv2: ";
                // tv2.print(std::cout);
                // std::cout << std::endl;
                if (tv1 > tv2) {
                    return (opType == BinaryOperationType::BOP_MINIMUM) ? e2 : e1;
                } else {
                    return (opType == BinaryOperationType::BOP_MINIMUM) ? e1 : e2;
                }
            }
        } else if (isTerminal(e2.getEdgeHandle())) {
            if (e2.isConstantPosInf()) {
                return (opType == BinaryOperationType::BOP_MINIMUM) ? e1 : e2;
            } else if (e2.isConstantNegInf()) {
                return (opType == BinaryOperationType::BOP_MINIMUM) ? e2 : e1;
            } else if (e1.isConstantUnDef()) {
                // TBD for UnDef
            }
        }
        /* Base case 3: two edges are the same edgeHandle but different edge value, only for EV+ */
    #ifdef BRAVE_DD_OPERATION_TRACE
        std::cout << "\tchecking base case 3\n";
    #endif
        if ((e1.getEdgeHandle() == e2.getEdgeHandle()) && (e1.getValue() != e2.getValue()) && (resForest->setting.getEncodeMechanism() != EDGE_PLUSMOD)) {
            if (e1.getValue() > e2.getValue()) {
                return (opType == BinaryOperationType::BOP_MINIMUM) ? e2 : e1;
            } else {
                return (opType == BinaryOperationType::BOP_MINIMUM) ? e1 : e2;
            }
        }
    /* -------------------------------------------------------------------------------------------------
    * Plus and Minus operations
    * ------------------------------------------------------------------------------------------------*/
    } else if ((opType == BinaryOperationType::BOP_PLUS) || (opType == BinaryOperationType::BOP_MINUS)) {
        /* Base case 0: one edge is constant*/
    #ifdef BRAVE_DD_OPERATION_TRACE
        std::cout << "\tchecking base case 0\n";
    #endif
        if (isTerminal(e1.getEdgeHandle())) {
            if (e1.isConstantOmega()) {
                // for EV
                ans = e2;
                ans.setValue(e1.getValue() + e2.getValue());
                return ans;
            } else if (e1.isConstantPosInf() || e1.isConstantNegInf()) {
                return e1;
            } else if (e1.isConstantUnDef()) {
                // TBD for UnDef
            } else if (isTerminal(e2.getEdgeHandle())) {
                // for MT
                Value tv1 = getTerminalValue(e1.getEdgeHandle());
                Value tv2 = getTerminalValue(e2.getEdgeHandle());
                EdgeHandle constant = makeTerminal(tv1 + tv2);
                packRule(constant, RULE_X);
                ans.setEdgeHandle(constant);
                ans = resForest->normalizeEdge(lvl, ans);
                return ans;
            }
        } else if (isTerminal(e2.getEdgeHandle())) {
            if (e2.isConstantOmega()) {
                // for EV
                ans = e1;
                ans.setValue(e1.getValue() + e2.getValue());
                return ans;
            } else if (e2.isConstantPosInf() || e2.isConstantNegInf()) {
                return e2;
            } else if (e2.isConstantUnDef()) {
                // TBD for UnDef
            }
        }
    /* -------------------------------------------------------------------------------------------------
    * Multiply operations
    * ------------------------------------------------------------------------------------------------*/
    } else if (opType == BinaryOperationType::BOP_MULTIPLY) {
        //
    } else {
        //
    }
    /* -------------------------------------------------------------------------------------------------
    * Reordering
    * ------------------------------------------------------------------------------------------------*/
    Level m1, m2;
    m1 = e1.getNodeLevel();
    m2 = e2.getNodeLevel();
    if (m1<m2) {
        SWAP(e1, e2);
        SWAP(m1, m2);
    }
    /* -------------------------------------------------------------------------------------------------
    * Check cache
    * ------------------------------------------------------------------------------------------------*/
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\tchecking cache\n";
#endif
    Value originalVal;
    if ((resForest->setting.getEncodeMechanism() != EDGE_PLUSMOD)   // not for EVmod
        && ((opType == BinaryOperationType::BOP_MINIMUM) || (opType == BinaryOperationType::BOP_MAXIMUM))) {  // not for Plus
        if (e1.getValue() < e2.getValue()) {
            originalVal = e1.getValue();
            e1.setValue(0);
            e2.setValue(e2.getValue() - originalVal);
        } else {
            originalVal = e2.getValue();
            e2.setValue(0);
            e1.setValue(e1.getValue() - originalVal);
        }
    }
    // protect edges
    // ProtectEdge pe1(resForest, e1);
    // ProtectEdge pe2(resForest, e2);
    
    if (caches[0].check(lvl, e1, e2, ans) && !resForest->getSetting().isRelation()) {
        if (!ans.isConstantPosInf() && !ans.isConstantNegInf()) ans.setValue(originalVal + ans.getValue());
        return ans;
    } else if (caches[0].check(m1, e1, e2, ans) && resForest->getSetting().isRelation()) {
        EdgeLabel root = 0;
        if (e1.getRule() == e2.getRule()) {
            packRule(root, e1.getRule());
            ans = resForest->mergeEdge(lvl, m1, root, ans);
        } else if (opType == BinaryOperationType::BOP_INTERSECTION) {
            // assuming I1 is not considered, TBD
            if (lvl-m1 == 0) {
                packRule(root, RULE_X);
            } else {
                packRule(root, RULE_I0);
            }
            ans = resForest->mergeEdge(lvl, m1, root, ans);
        } else {
            // for operation like UNION
            packRule(root, RULE_X);
            std::vector<Edge> tmp(4);
            if (isRuleI(e1.getRule())) {
                tmp[1] = e2;
                tmp[2] = e2;
            } else {
                tmp[1] = e1;
                tmp[2] = e1;
            }
            tmp[1].setRule(RULE_X);
            tmp[2].setRule(RULE_X);
            for (Level k=m1+1; k<=lvl; k++) {
                tmp[0] = ans;
                tmp[3] = ans;
                ans = resForest->reduceEdge(k, root, k, tmp);
            }
        }
        if (!ans.isConstantPosInf() && !ans.isConstantNegInf()) ans.setValue(originalVal + ans.getValue());
        return ans;
    }
    /* -------------------------------------------------------------------------------------------------
    * Compute 
    * ------------------------------------------------------------------------------------------------*/
    // Here means we can not find the result in cache, computation is needed
    // Case that edge1 is a short edge
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\tcheck if recursive computing\n";
#endif

    if (resForest->getSetting().hasReductionRule(RULE_00)) {
        // Do not change this
        if (m1 == lvl) {
        // if (true) {
            ans = operateS(lvl, lvl, e1, e2);

            cacheAdd(0, lvl, e1, e2, ans);
            return ans;
        }
        // lvl > m1 >= m2
        ReductionRule r1 = e1.getRule();
        ReductionRule r2 = e2.getRule();
        bool canISkip = false;

        if (r1 == RULE_X || r2 == RULE_X) canISkip = true; 

        if (r1 == RULE_00 && r1 == RULE_00) {
            Edge targetChild1 = resForest->cofact(m1, e1, 0);
            Edge targetChild2 = resForest->cofact(m1, e2, 0);
            if (targetChild1.getRule() == RULE_X
            && targetChild1.getNodeLevel() + 1 < m1) canISkip = true;
            if (targetChild2.getRule() == RULE_X
            && targetChild2.getNodeLevel() + 1 < m1) canISkip = true;
        }
        if (r1 == RULE_11 && r2 == RULE_11) {
            Edge targetChild1 = resForest->cofact(m1, e1, 1);
            Edge targetChild2 = resForest->cofact(m1, e2, 1);
            if (targetChild1.getRule() == RULE_X
            && targetChild1.getNodeLevel() + 1 < m1) canISkip = true;
            if (targetChild2.getRule() == RULE_X
            && targetChild2.getNodeLevel() + 1 < m1) canISkip = true;
        }

        if (!canISkip && r1 == r2) {
            Edge tc1 = resForest->cofact(m1, e1, r1 == RULE_11);
            Edge tc2 = resForest->cofact(m1, e2, r2 == RULE_11);
            ReductionRule tr1 = tc1.getRule();
            ReductionRule tr2 = tc2.getRule();
            if (tr1 == RULE_X) canISkip = true;
            if (tr2 == RULE_X) canISkip = true;
        }

        if (canISkip && r1 != r2) {
            canISkip = false;
        }

        if (!canISkip) {
            ans = operateS(lvl, lvl, e1, e2);      
            cacheAdd(0, lvl, e1, e2, ans);
            return ans;
        }

        Level cofactLvl;
        if (r1 == RULE_X) {
            if (r2 == RULE_X) {
                cofactLvl = m1;
                ans = operateS(lvl, cofactLvl, e1, e2);
            } else if (r2 == RULE_00 || r2 == RULE_11) {
                cofactLvl = m1+1;
                ans = operateS(lvl, cofactLvl, e2, e1);
            }           
        } else if (r1 == RULE_00 || r1 == RULE_11) {
            if (r2 == RULE_X) {
                cofactLvl = m1 > m2 ? m1 : m1 + 1;
                ans = operateS(lvl, cofactLvl, e1, e2);      
            } else if (r2 == RULE_00 || r2 == RULE_11) {
                cofactLvl = m1+1;
                if (r1 == r2) {
                    ans = operateS(lvl, cofactLvl, e1, e2);
                } else {
                    std::cout << "nono" << std::endl;    
                }
            }         
        } else {
            std::cout << "I guess we have a missing case lol" << std::endl;
            exit(0);
        }

        cacheAdd(0, lvl, e1, e2, ans);
        return ans;
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << std::endl;
    std::cout << "rule1: " << rule2String(r1) << " rule2: " << rule2String(r2) << std::endl;
    std::cout << "child 1: ";
    child1[0].print(std::cout);
    std::cout << " , ";
    child1[1].print(std::cout);
    std::cout << std::endl;
    std::cout << "child 2: ";
    child2[0].print(std::cout);
    std::cout << " , ";
    child2[1].print(std::cout);
    std::cout << std::endl;
#endif    
    }
    if (m1 == lvl) {
        std::vector<Edge> child1, child2, tmp;
        if (resForest->getSetting().isRelation()) {
            child1 = std::vector<Edge>(4);
            child2 = std::vector<Edge>(4);
            tmp = std::vector<Edge>(4);
        } else {
            child1 = std::vector<Edge>(2);
            child2 = std::vector<Edge>(2);
            tmp = std::vector<Edge>(2);
        }
        for (size_t i=0; i<child1.size(); i++) {
            child1[i] = resForest->cofact(lvl, e1, i);
            child2[i] = resForest->cofact(lvl, e2, i);
            tmp[i] = computeElmtWise(lvl-1, child1[i], child2[i]);
        }
        EdgeLabel root = 0;
        packRule(root, RULE_X);
        ans = resForest->reduceEdge(lvl, root, lvl, tmp);

        // ProtectEdge protectAns(resForest, ans);

        // save to cache
        cacheAdd(0, lvl, e1, e2, ans);
        if (!ans.isConstantPosInf() && !ans.isConstantNegInf()) ans.setValue(originalVal + ans.getValue());
        return ans;
    }
    /* -------------------------------------------------------------------------------------------------
    * Compute
    * ------------------------------------------------------------------------------------------------*/
    // Here we have lvl>m1>=m2
    if (!resForest->getSetting().isRelation()) {
        // For BDDs, it's time to decide pattern types and use pattern operations
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\tpatterns computing\n";
#endif
        char t1, t2;
        t1 = rulePattern(e1.getRule());
        t2 = rulePattern(e2.getRule());
        bool canISkip = 0;
        if (t1 == 'L') {
            if (t2 == 'L') {
               canISkip = true; 
            } 
        } else if (t1 == 'H') {
            if (t2 == 'H') {
               canISkip = true; 
            } 
        } else {
            if (t2 == 'U') {
               canISkip = true; 
            }
        }
        if (!canISkip) {
            ans = operateS(lvl, lvl, e1, e2);      
            cacheAdd(0, lvl, e1, e2, ans);
            return ans;
        }
        if (t1 == 'L') {
            if (t2 == 'L' || t2 == 'U') {
                ans = operateLL(lvl, e1, e2);
            } else {
                ans = operateLH(lvl, e1, e2);
            }
        } else if (t1 == 'H') {
            if (t2 == 'H' || t2 == 'U') {
                ans = operateHH(lvl, e1, e2);
            } else {
                ans = operateLH(lvl, e2, e1);
            }
        } else {
            if (t2 == 'L' || t2 == 'U') {
                ans = operateLL(lvl, e1, e2);
            } else {
                ans = operateHH(lvl, e1, e2);
            }
        }
        // save cache
        cacheAdd(0, lvl, e1, e2, ans);
        if (!ans.isConstantPosInf() && !ans.isConstantNegInf()) ans.setValue(originalVal + ans.getValue());
        return ans;
    } else {
        // For MXDs, recursively compute the bottom part, then cache and merge
        std::vector<Edge> child1(4), child2(4), tmp(4);
        for (char i=0; i<(char)child1.size(); i++) {
            child1[i] = resForest->cofact(m1, e1, i);
            child2[i] = resForest->cofact(m1, e2, i);
            tmp[i] = computeElmtWise(m1-1, child1[i], child2[i]);
        }
        EdgeLabel root = 0;
        packRule(root, RULE_X);
        ans = resForest->reduceEdge(m1, root, m1, tmp);
        // save to cache
        cacheAdd(0, m1, e1, e2, ans);
        // merge edge
        if (e1.getRule() == e2.getRule()) {
            packRule(root, e1.getRule());
            ans = resForest->mergeEdge(lvl, m1, root, ans);
        } else if (opType == BinaryOperationType::BOP_INTERSECTION) {
            // assuming I1 is not considered, TBD
            packRule(root, RULE_I0);
            ans = resForest->mergeEdge(lvl, m1, root, ans);
        } else {
            // for operation like UNION
            packRule(root, RULE_X);
            if (isRuleI(e1.getRule())) {
                tmp[1] = e2;
                tmp[2] = e2;
            } else {
                tmp[1] = e1;
                tmp[2] = e1;
            }
            tmp[1].setRule(RULE_X);
            tmp[2].setRule(RULE_X);
            for (Level k=m1+1; k<=lvl; k++) {
                tmp[0] = ans;
                tmp[3] = ans;
                ans = resForest->reduceEdge(k, root, k, tmp);
            }
        }
        if (!ans.isConstantPosInf() && !ans.isConstantNegInf()) ans.setValue(originalVal + ans.getValue());
        return ans;
    }
}


Edge BinaryOperation::computeUnion(const Level lvl, const Edge& source1, const Edge& source2)
{
    Edge ans;
    Edge e1, e2;
    // normalize edges
    e1 = resForest->normalizeEdge(lvl, source1);
    e2 = resForest->normalizeEdge(lvl, source2);

    // Base case 1: two edges are the same
    if (e1 == e2) return e1;
    // Base case 2: two edges are complemented
    // Base case 3: one edge is constant ONE edge
    if (e1.isComplementTo(e2) || e1.isConstantOne() || e2.isConstantOne()) {
        EdgeHandle constant = makeTerminal(INT, 1);
        if (resForest->getSetting().getValType() == FLOAT) {
            constant = makeTerminal(FLOAT, 1.0f);
        }
        packRule(constant, RULE_X);
        ans.setEdgeHandle(constant);
        ans = resForest->normalizeEdge(lvl, ans);
        return ans;
    }
    // Base case 4: one edge is constant ZERO edge
    if (e1.isConstantZero()) return e2;
    if (e2.isConstantZero()) return e1;

    Level m1, m2;
    m1 = e1.getNodeLevel();
    m2 = e2.getNodeLevel();
    // ordering
    if (m1<m2) {
        SWAP(e1, e2);
        SWAP(m1, m2);
    }
    
    // check cache here
    if (caches[0].check(lvl, e1, e2, ans)) return ans;

    // Case that edge1 is a short edge
    if (m1 == lvl) {
        Edge x1, y1, x2, y2;
        x1 = resForest->cofact(lvl, e1, 0);
        y1 = resForest->cofact(lvl, e1, 1);
        x2 = resForest->cofact(lvl, e2, 0);
        y2 = resForest->cofact(lvl, e2, 1);
        std::vector<Edge> child(2);
        child[0] = computeUnion(lvl-1, x1, x2);
        child[1] = computeUnion(lvl-1, y1, y2);
        EdgeLabel root = 0;
        packRule(root, RULE_X);
        ans = resForest->reduceEdge(lvl, root, lvl, child);

        // save to cache
        cacheAdd(0, lvl, e1, e2, ans);
        return ans;
    }

    // Here we have m1>=m2, it's time to decide pattern types and use pattern operations
    char t1, t2;
    t1 = rulePattern(e1.getRule());
    t2 = rulePattern(e2.getRule());
    if (t1 == 'L') {
        if (t2 == 'L' || t2 == 'U') {
            ans = operateLL(lvl, e1, e2);
        } else {
            ans = operateLH(lvl, e1, e2);
        }
    } else if (t1 == 'H') {
        if (t2 == 'H' || t2 == 'U') {
            ans = operateHH(lvl, e1, e2);
        } else {
            ans = operateLH(lvl, e2, e1);
        }
    } else {
        if (t2 == 'L' || t2 == 'U') {
            ans = operateLL(lvl, e1, e2);
        } else {
            ans = operateHH(lvl, e1, e2);
        }
    }
    // save cache
    cacheAdd(0, lvl, e1, e2, ans);
    return ans;
}

Edge BinaryOperation::computeIntersection(const Level lvl, const Edge& source1, const Edge& source2)
{
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "compute INTERSECTION: lvl: " << lvl << "; e1: ";
    source1.print(std::cout);
    std::cout << "; e2: ";
    source2.print(std::cout);
    std::cout << std::endl;
#endif

    Edge ans;
    Edge e1, e2;
    // normalize edges
    e1 = resForest->normalizeEdge(lvl, source1);
    e2 = resForest->normalizeEdge(lvl, source2);

    // Base case 1: two edges are the same
    if (e1 == e2) return e1;
    // Base case 2: two edges are complemented
    // Base case 3: one edge is constant ZERO edge
    if (e1.isComplementTo(e2) || e1.isConstantZero() || e2.isConstantZero()) {
        EdgeHandle constant = makeTerminal(INT, 0);
        if (resForest->getSetting().getValType() == FLOAT) {
            constant = makeTerminal(FLOAT, 0.0f);
        }
        packRule(constant, RULE_X);
        ans.setEdgeHandle(constant);
        ans = resForest->normalizeEdge(lvl, ans);
        return ans;
    }
    // Base case 4: one edge is constant ONE edge
    if (e1.isConstantOne()) return e2;
    if (e2.isConstantOne()) return e1;

    Level m1, m2;
    m1 = e1.getNodeLevel();
    m2 = e2.getNodeLevel();
    // ordering
    if (m1 < m2) {
        SWAP(e1, e2);
        SWAP(m1, m2);
    }
    
    // check cache here
    if (caches[0].check(lvl, e1, e2, ans)) return ans;

    // Case that edge1 is a short edge
    if (m1 == lvl) {
        Edge x1, y1, x2, y2;
        x1 = resForest->cofact(lvl, e1, 0);
        y1 = resForest->cofact(lvl, e1, 1);
        x2 = resForest->cofact(lvl, e2, 0);
        y2 = resForest->cofact(lvl, e2, 1);
        std::vector<Edge> child(2);
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\trecursive 0 from level: " << lvl << std::endl;
#endif
        child[0] = computeIntersection(lvl-1, x1, x2);
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\trecursive 1 from level: " << lvl << std::endl;
#endif
        child[1] = computeIntersection(lvl-1, y1, y2);
        EdgeLabel root = 0;
        packRule(root, RULE_X);
        ans = resForest->reduceEdge(lvl, root, lvl, child);

        // save to cache
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\tcase 1: save to cache: ";
    ans.print(std::cout);
    std::cout << std::endl;
#endif
        cacheAdd(0, lvl, e1, e2, ans);
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\tsave done\n";
#endif
        return ans;
    }

    // Here we have m1>=m2, it's time to decide pattern types and use pattern operations
    char t1, t2;
    t1 = rulePattern(e1.getRule());
    t2 = rulePattern(e2.getRule());
    if (t1 == 'L') {
        if (t2 == 'L' || t2 == 'U') {
            ans = operateLL(lvl, e1, e2);
        } else {
            ans = operateLH(lvl, e1, e2);
        }
    } else if (t1 == 'H') {
        if (t2 == 'H' || t2 == 'U') {
            ans = operateHH(lvl, e1, e2);
        } else {
            ans = operateLH(lvl, e2, e1);
        }
    } else {
        if (t2 == 'L' || t2 == 'U') {
            ans = operateLL(lvl, e1, e2);
        } else {
            ans = operateHH(lvl, e1, e2);
        }
    }
    // save cache
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\tcase 2: save to cache: ";
    ans.print(std::cout);
    std::cout << std::endl;
#endif
    cacheAdd(0, lvl, e1, e2, ans);
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\tsave done\n";
#endif
    return ans;
}

Edge BinaryOperation::computeImage(const Level lvl, const Edge& source1, const Edge& trans, bool isPre)
{
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << ((isPre)?"Pre":"Post") << "IMAGE: lvl: " << (Level)lvl << "; s: ";
    source1.print(std::cout);
    std::cout << "; r: ";
    trans.print(std::cout);
    std::cout << std::endl;
#endif

    Edge ans;
    Edge s, r;
    // normalize edges
    s = source1Forest->normalizeEdge(lvl, source1);
    r = source2Forest->normalizeEdge(lvl, trans);

    // Base case 1: empty state or relation
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\tchecking base case 1\n";
#endif
    if (s.isConstantZero()
        || (s.isConstantOmega() && s.getValue() == Value(0))
        || r.isConstantZero()) {
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\t\tbase case 1\n";
#endif
        if (source1Forest->setting.getEncodeMechanism() == TERMINAL) {
            EdgeHandle constant = makeTerminal(INT, 0);
            if (source1Forest->getSetting().getValType() == FLOAT) {
                constant = makeTerminal(FLOAT, 0.0f);
            }
            packRule(constant, RULE_X);
            ans.setEdgeHandle(constant);
        } else {
            EdgeHandle constant = makeTerminal(VOID, SpecialValue::OMEGA);
            packRule(constant, RULE_X);
            ans.setEdgeHandle(constant);
        }
        ans = source1Forest->normalizeEdge(lvl, ans);
        return ans;
    }

    // Base case 2: identity or redundant relation
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\tchecking base case 2\n";
#endif
    if (r.getNodeLevel() == 0) {
        if ((r.getRule() == RULE_I0) && (isTerminalOne(r.getEdgeHandle()) || isTerminalZero(r.getEdgeHandle())) && (r.getComp() ^ isTerminalOne(r.getEdgeHandle()))) {
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\t\tbase case 2: identity\n";
#endif
            return s;
        } else if (r.isConstantOne()) {
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\t\tbase case 2: redundant\n";
#endif
        if (source1Forest->setting.getEncodeMechanism() == TERMINAL) {
            EdgeHandle constant = makeTerminal(INT, 1);
            if (source1Forest->getSetting().getValType() == FLOAT) {
                constant = makeTerminal(FLOAT, 1.0f);
            }
            packRule(constant, RULE_X);
            ans.setEdgeHandle(constant);
        } else {
            EdgeHandle constant = makeTerminal(VOID, SpecialValue::OMEGA);
            packRule(constant, RULE_X);
            ans.setEdgeHandle(constant);
            ans.setValue(1);
        }
            ans = source1Forest->normalizeEdge(lvl, ans);
            return ans;
        }
    }

    Level m = (s.getNodeLevel() > r.getNodeLevel()) ? s.getNodeLevel() : r.getNodeLevel();
    // assertion: m>0
    Edge sCache = s;
    Edge rCache = r;
    if (s.getNodeLevel() == m) sCache.setRule(RULE_X);
    if (r.getNodeLevel() == m) rCache.setRule(RULE_X);
    // check cache
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\tchecking cache\n";
#endif
    if (!caches[0].check(m, sCache, rCache, ans)) {
        // -----------------------------------------------------------
        // protect edge
        // ProtectEdge protectS(source1Forest, sCache);
        // std::vector<Edge> protectChild;
        // std::vector<Edge> protectRec;
        // -----------------------------------------------------------
        // not cached, computing needed
        std::vector<Edge> child(2);
        EdgeHandle constant = makeTerminal(INT, 0);
        if (source1Forest->getSetting().getValType() == FLOAT) {
            constant = makeTerminal(FLOAT, 0.0f);
        }
        if (source1Forest->setting.getEncodeMechanism() != TERMINAL) {
            constant = makeTerminal(VOID, SpecialValue::OMEGA);
        }
        packRule(constant, RULE_X);
        for (size_t i=0; i<2; i++) {
            child[i].setEdgeHandle(constant);
            child[i] = source1Forest->normalizeEdge(m-1, child[i]);
        }
        if ((m > r.getNodeLevel()) && (r.getRule() == RULE_I0)) {
            Edge rr = r;
            if (m-r.getNodeLevel() == 1) rr.setRule(RULE_X);
            child[0] = computeImage(m-1, source1Forest->cofact(m, s, 0), rr);
            // protectChild.push_back(child[0]);
            // source1Forest->registerEdge(child[0]);

            child[1] = computeImage(m-1, source1Forest->cofact(m, s, 1), rr);
            // protectChild.push_back(child[1]);
            // source1Forest->registerEdge(child[1]);
        } else {
            // recursive computing
            Edge sRec, rRec, resRec;
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\trecursive computing\n";
#endif
            // Union of BDDs operation required
            BinaryOperationType unionType = BinaryOperationType::BOP_UNION;
            if (source1Forest->setting.getEncodeMechanism() != TERMINAL) unionType = BinaryOperationType::BOP_MAXIMUM;
            BinaryOperation* un = BOPs.find(unionType, source1Forest, source1Forest, source1Forest);
            if (!un) {
                un = BOPs.add(new BinaryOperation(unionType, source1Forest, source1Forest, source1Forest));
            }
            for (char i=0; i<4; i++) {
                // if ((r.getRule() == RULE_I0) && (s.getNodeLevel() > m) && (i == 1 || i == 2)) continue;
                char s0Idx = (isPre) ? (i&(0x01)) : ((i&(0x01<<1))>>1);
                char s1Idx = (isPre) ? ((i&(0x01<<1))>>1) : (i&(0x01));
                sRec = source1Forest->cofact(m, s, s0Idx);
                rRec = source2Forest->cofact(m, r, i);
                resRec = computeImage(m-1, sRec, rRec, isPre);
                // protectRec.push_back(resRec);
                // source1Forest->registerEdge(resRec);

                child[s1Idx] = un->computeElmtWise(m-1, child[s1Idx], resRec);
                // protectChild.push_back(child[s1Idx]);
                // source1Forest->registerEdge(child[s1Idx]);
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "after union child[" << (int)s1Idx << "]: ";
    child[s1Idx].print(std::cout);
    std::cout << std::endl;
#endif
            }
        }
        EdgeLabel root = 0;
        packRule(root, RULE_X);
        ans = source1Forest->reduceEdge(m, root, m, child);
        // ----------------------------------------------------------- 
        // // protect ans
        // ProtectEdge protectAns(resForest, ans);
        // // unprotect edges
        // for (size_t i=0; i<protectChild.size(); i++) {
        //     source1Forest->deregisterEdge(protectChild[i]);
        // }
        // for (size_t i=0; i<protectRec.size(); i++) {
        //     source1Forest->deregisterEdge(protectRec[i]);
        // }
        // -----------------------------------------------------------
        // cache
        cacheAdd(0, m, sCache, rCache, ans);
    }
    // merge with the incoming edge rule
    EdgeLabel incoming = 0;
    packRule(incoming, (r.getRule() == RULE_I0)?s.getRule():RULE_X);    // TBD for rex
    ans = source1Forest->mergeEdge(lvl, m, incoming, ans);
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "after " << ((isPre)?"Pre":"Post") << "IMAGE: lvl: " << lvl << "; s: ";
    source1.print(std::cout);
    std::cout << "; r: ";
    trans.print(std::cout);
    std::cout << std::endl;
    std::cout << "\tresult: ";
    ans.print(std::cout);
    std::cout << std::endl;
#endif
    return ans;
}

Edge BinaryOperation::operateLL(const Level lvl, const Edge& e1, const Edge& e2)
{
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "operateLL: lvl: " << lvl << "; e1: ";
    e1.print(std::cout);
    std::cout << "; e2: ";
    e2.print(std::cout);
    std::cout << std::endl;
#endif

    Level m1, m2;
    m1 = e1.getNodeLevel();
    m2 = e2.getNodeLevel();

    Edge x1, x2, y1, y2;
    x1 = e1.part(0);
    x2 = e2.part(0);
    y1 = e1.part(1);
    y2 = (m1==m2) ? e2.part(1) : resForest->cofact(m1+1, e2, 1);

    Edge x, y;
    x = computeElmtWise(m1, x1, x2);
    y = computeElmtWise(m1, y1, y2);
    Edge ans = resForest->buildHalf(lvl, m1+1, x, y, 1);
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "build Low with x: ";
    x.print(std::cout);
    std::cout << "; y: ";
    y.print(std::cout);
    std::cout << std::endl;
    std::cout << "after operateHH from lvl: " << lvl << "; result: ";
    ans.print(std::cout);
    std::cout << std::endl;
#endif
    return ans;
}

Edge BinaryOperation::operateHH(const Level lvl, const Edge& e1, const Edge& e2)
{
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "operateHH: lvl: " << lvl << "; e1: ";
    e1.print(std::cout);
    std::cout << "; e2: ";
    e2.print(std::cout);
    std::cout << std::endl;
#endif
    Level m1, m2;
    m1 = e1.getNodeLevel();
    m2 = e2.getNodeLevel();

    Edge x1, x2, y1, y2;
    x1 = e1.part(0);
    x2 = (m1==m2) ? e2.part(0) : resForest->cofact(m1+1, e2, 0);
    y1 = e1.part(1);
    y2 = e2.part(1);

    Edge x, y;
    x = computeElmtWise(m1, x1, x2);
    y = computeElmtWise(m1, y1, y2);
    Edge ans = resForest->buildHalf(lvl, m1+1, x, y, 0);
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "build High with x: ";
    x.print(std::cout);
    std::cout << "; y: ";
    y.print(std::cout);
    std::cout << std::endl;
    std::cout << "after operateHH from lvl: " << lvl << "; result: ";
    ans.print(std::cout);
    std::cout << std::endl;
#endif
    return ans;

}

Edge BinaryOperation::operateLH(const Level lvl, const Edge& e1, const Edge& e2)
{
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "operateLH: lvl: " << lvl << "; e1: ";
    e1.print(std::cout);
    std::cout << "; e2: ";
    e2.print(std::cout);
    std::cout << std::endl;
#endif
    Level m1, m2, m;
    m1 = e1.getNodeLevel();
    m2 = e2.getNodeLevel();

    Edge x1, x2, y1, y2;
    x1 = e1.part(0);
    y2 = e2.part(1);
    if (m1 == m2) {
        y1 = e1.part(1);
        x2 = e2.part(0);
        m = m1;
    } else if (m1>m2) {
        y1 = e1.part(1);
        x2 = resForest->cofact(m1+1, e2, 0);
        m = m1;
    } else {
        y1 = resForest->cofact(m2+1, e1, 1);
        x2 = e2.part(0);
        m = m2;
    }
    Edge x, y, z;
    x = computeElmtWise(m, x1, x2);
    z = computeElmtWise(m, y1, y2);
    if (lvl - m == 1) {
        EdgeLabel root = 0;
        packRule(root, RULE_X);
        std::vector<Edge> child(2);
        child[0] = x;
        child[1] = z;
        Edge ans = resForest->reduceEdge(lvl, root, lvl, child);
        return ans;
    }
    y = computeElmtWise(m, x1, y2);
    Edge ans = resForest->buildUmb(lvl, m+1, x, y, z);
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "build Umbrella with x: ";
    x.print(std::cout);
    std::cout << "; y: ";
    y.print(std::cout);
    std::cout << "; z: ";
    z.print(std::cout);
    std::cout << std::endl;
    std::cout << "after operateHH from lvl: " << lvl << "; result: ";
    ans.print(std::cout);
    std::cout << std::endl;
#endif
    return ans;
}

Edge BinaryOperation::operateS(const Level lvl, const Level clvl, const Edge& e1, const Edge& e2)
{
    std::vector<Edge> child(2);
    for (char i=0; i<2; i++) {
        Edge p = resForest->cofact(clvl, e1, i);
        Edge q = resForest->cofact(clvl, e2, i);
        child[i] = computeElmtWise(clvl-1, p, q);
    }

    EdgeLabel root=0;
    packRule(root, e1.getRule());
    if (lvl == clvl) packRule(root, RULE_X);
    
    Edge ans = resForest->reduceEdge(lvl, root, clvl, child);
    return ans;
}

// We assume that e1 is 00
Edge BinaryOperation::operateD(const Level lvl, const Level clvl, const Edge& e1, const Edge& e2)
{
    std::vector<Edge> oChild(2);
    std::vector<Edge> aChild(2);
    
    Edge p = resForest->cofact(clvl, e1, 0);
    Edge q = resForest->cofact(clvl, e1, 1);
    Edge r = resForest->cofact(clvl, e2, 0);
    Edge s = resForest->cofact(clvl, e2, 1);

    std::vector<Edge> child1(2);
    child1[0] = computeElmtWise(clvl-1, p, r);
    child1[1] = computeElmtWise(clvl-1, p, s);

    std::vector<Edge> child2(2);
    child2[0] = child1[1];
    child2[1] = computeElmtWise(clvl-1, q, s);

    std::vector<Edge> child(2);
    EdgeLabel root1=0;
    packRule(root1, RULE_11);
    if (lvl-1 == clvl) {
        packRule(root1, RULE_X);
    }
    child[0] = resForest->reduceEdge(lvl-1, root1, clvl, child1);


    EdgeLabel root2=0;
    packRule(root2, RULE_00);
    child[1] = resForest->reduceEdge(lvl-1, root2, clvl, child2);

    EdgeLabel root3=0;
    packRule(root3, RULE_X);
    Edge ans = resForest->reduceEdge(lvl, root3, lvl, child);
    return ans;
}// ******************************************************************
// *                                                                *
// *                       BinaryList  methods                      *
// *                                                                *
// ******************************************************************
BinaryList::BinaryList(const std::string n)
{
    reset(n);
}

BinaryOperation* BinaryList::mtfBinary(const BinaryOperationType opT, const Forest* source1F, const Forest* source2F, const Forest* resF)
{
    BinaryOperation* prev = front;
    BinaryOperation* curr = front->next;
    while (curr) {
        if ((curr->opType == opT) && (curr->source1Forest == source1F) && (curr->source2Forest == source2F) && (curr->resForest == resF)) {
            // Move to front
            prev->next = curr->next;
            curr->next = front;
            front = curr;
            return curr;
        }
        prev = curr;
        curr = curr->next;
    }
    return nullptr;
}

BinaryOperation* BinaryList::mtfBinary(const BinaryOperationType opT, const Forest* source1F, const OpndType source2T, const Forest* resF)
{
    BinaryOperation* prev = front;
    BinaryOperation* curr = front->next;
    while (curr) {
        if ((curr->opType == opT) && (curr->source1Forest == source1F) && (curr->source2Type == source2T) && (curr->resForest == resF)) {
            // Move to front
            prev->next = curr->next;
            curr->next = front;
            front = curr;
            return curr;
        }
        prev = curr;
        curr = curr->next;
    }
    return nullptr;
}

void BinaryList::searchRemove(BinaryOperation* bop)
{
    if (!front) return;
    BinaryOperation* prev = front;
    BinaryOperation* curr = front->next;
    while (curr) {
        if (curr == bop) {
            prev->next = curr->next;
            delete curr;
            return;
        }
        prev = curr;
        curr = curr->next;
    }
}

void BinaryList::searchRemove(Forest* forest)
{
    if (!front || !forest) return;
    // check front first
    while (front && ((front->source1Forest == forest) || (front->source2Forest == forest) || (front->resForest == forest))) {
        BinaryOperation* toRemove = front;
        front = front->next;
        delete toRemove;
    }
    // check the remaining
    BinaryOperation* curr = front;
    while (curr && curr->next) {
        if ((curr->next->source1Forest == forest) || (curr->next->source2Forest == forest) || (curr->next->resForest == forest)) {
            BinaryOperation* toRemove = curr->next;
            curr->next = curr->next->next;
            delete toRemove;
        } else {
            curr = curr->next;
        }
    }
}

void BinaryList::searchSweepCache(Forest* forest)
{
    if (!front || !forest) return;
    BinaryOperation* curr = front;
    bool isSource1 = curr->source1Forest == forest;
    bool isSource2 = curr->source2Forest == forest;
    bool isRes = curr->resForest == forest;
    while (curr) {
        if (isSource1 || isSource2 || isRes) {
            // sweep cache
            if ((curr->opType == BinaryOperationType::BOP_PREIMAGE) || (curr->opType == BinaryOperationType::BOP_POSTIMAGE)) {
                if (isSource1) {
                    curr->caches[0].sweep(forest, 0);
                    curr->caches[0].sweep(forest, 1);
                }
                if (isSource2) {
                    curr->caches[0].sweep(forest, 2);
                }

            } else if ((curr->opType == BinaryOperationType::BOP_UNION)
                        || (curr->opType == BinaryOperationType::BOP_INTERSECTION)
                        || (curr->opType == BinaryOperationType::BOP_MINIMUM)
                        || (curr->opType == BinaryOperationType::BOP_MAXIMUM)
                        || (curr->opType == BinaryOperationType::BOP_PLUS)
                        || (curr->opType == BinaryOperationType::BOP_MINUS)) {
                if (isRes) {
                    curr->caches[0].sweep(forest, 0);
                    curr->caches[0].sweep(forest, 1);
                    curr->caches[0].sweep(forest, 2);
                }
            }
            // other operations TBD
        }
        curr = curr->next;
        if (curr) {
            isSource1 = curr->source1Forest == forest;
            isSource2 = curr->source2Forest == forest;
            isRes = curr->resForest == forest;
        }
    }
}

void BinaryList::reportCacheStat(std::ostream& out, int format) const
{
    BinaryOperation* curr = front;
    uint64_t n = 0;
    out << "BinaryList:\n";
    while (curr) {
        out << "CT " << n << " =============================\n";
        out << "Source1 Forest: " << curr->source1Forest->getSetting().getName() << "\n";
        out << "Source2 Forest: " << curr->source2Forest->getSetting().getName() << "\n";
        out << "Result Forest: " << curr->resForest->getSetting().getName() << "\n";
        out << "Operation Type: " << BOP2String(curr->opType) << "\n";
        out << "----------------------------------\n";
        curr->caches[0].reportStat(out, format);
        curr = curr->next;
        n++;
    }
}


// // ******************************************************************
// // *                                                                *
// // *                                                                *
// // *                 NumericalOperation  methods                    *
// // *                                                                *
// // *                                                                *
// // ******************************************************************
// NumericalOperation::NumericalOperation()
// {
//     //
// }

// ******************************************************************
// *                                                                *
// *                                                                *
// *                 SaturationOperation  methods                   *
// *                                                                *
// *                                                                *
// ******************************************************************
SaturationOperation::SaturationOperation(Forest* source1, Forest* source2, Forest* res)
{
    source1Forest = source1;
    source2Forest = source2;
    resForest = res;
    isPre = 0;
    caches.resize(2);
}

SaturationOperation::~SaturationOperation()
{
    caches.clear();
    source1Forest = nullptr;
    source2Forest = nullptr;
    resForest = nullptr;
    isPre = 0;
}

void SaturationOperation::setRelations(const std::vector<Func>& rels)
{
    relations = rels;
    sortRelations();
}

void SaturationOperation::setDirection(const bool dir)
{
    isPre = dir;
}

void SaturationOperation::sweepAndEnlarge(const size_t cacheID)
{
    // first check if number of entries reach to the thresholds
    double ratio = static_cast<double>(caches[cacheID].numEntries) / caches[cacheID].size;
    // std::cout << "[sweep and enlarge] in satuartion; ratio: " << ratio << std::endl;
    // ---------------------------------------------------------------------------------------------------------------
    // bool sweepDone = 0;
    // // it's time to sweep?
    // if ((ratio > thresholdsSweep)) {
    //     std::cout << "sweep saturation now... ratio: " << ratio ;
    //     // mark all resgitered function and protected edges
    //     source1Forest->markAllFuncs();
    //     source1Forest->markAllProtectedEdges();
    //     // sweep
    //     source1Forest->markSweep();
    //     sweepDone = 1;
    //     // update ratio
    //     ratio = static_cast<double>(caches[0].numEntries) / caches[0].size;
    //     std::cout << "after ratio: " << ratio << std::endl;
    // }
    // // it's time to enlarge?
    // if (sweepDone && (ratio > thresholdsEnlarge) && (caches[0].size < (uint64_t)0x01 << 62)) {
    // ---------------------------------------------------------------------------------------------------------------
    if ((ratio > thresholdsEnlarge) && (caches[cacheID].size < (uint64_t)0x01 << 62)) {
        caches[cacheID].size *= 2;
        caches[cacheID].enlarge(caches[cacheID].size);
    }
}

void SaturationOperation::compute(const Func& source1, Func& res)
{
    // check if the relations are compatible
    if (!checkForestCompatibility()) {
        throw error(ErrCode::INVALID_OPERATION, __FILE__, __LINE__);
        exit(ErrCode::INVALID_OPERATION);
    }
    Edge ans;
    Level numVars = resForest->getSetting().getNumVars();

#ifdef BRAVE_DD_PRINT_RELATIONS
    // print for test
    std::cout << "===========================================\n";
    for (size_t i=0; i<relations.size();i++) {
        relations[i].getEdge().print(std::cout);
        std::cout << std::endl;
    }
    // find all relations that Top is k
    std::vector<Func> rels;
    std::copy_if(relations.begin(), relations.end(), std::back_inserter(rels),
                [](Func& a) { return a.getEdge().getNodeLevel() == 15; });
    std::cout << "===========================================\n";
    for (size_t i=0; i<rels.size(); i++) {
        rels[i].getEdge().print(std::cout);
        std::cout << std::endl;
    }
#endif
    // exit(1);

    // Unary operation to copy from source1 forest to target forest
    UnaryOperation* cp1 = UOPs.find(UnaryOperationType::UOP_COPY, source1.getForest(), res.getForest());
    if (!cp1) {
        cp1 = UOPs.add(new UnaryOperation(UnaryOperationType::UOP_COPY, source1.getForest(), res.getForest()));
    }
    // compute the result
    /* Note: perhaps changing the relation functions of THIS operation will be called later.

                So, clean up or reconstruct the cache, TBD
    */
    if (resForest->setting.getRangeType() == BOOLEAN) {
        ans = computeSaturation(numVars, source1.getEdge(), 0);
    } else {
        ans = computeSaturationDistance(numVars, source1.getEdge(), 0);
    }
    Func ansEqu(source1.getForest(), ans);
    cp1->compute(ansEqu, res);
    return;
}

bool SaturationOperation::checkForestCompatibility() const
{
    bool ans = 1;
    // TBD
    return ans;
}

Edge SaturationOperation::computeSaturation(const Level lvl, const Edge& source1, const size_t begin)
{
    /* the result would go the same forest as source1 */
    // begin event's level should not be higher than lvl
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "computeSaturation: lvl " << lvl << "; ";
    source1.print(std::cout);
    std::cout << "; begin: " << begin << "; ";
    relations[begin].getEdge().print(std::cout);
    std::cout << std::endl;
    if (begin >= relations.size()) {
        std::cout << "out of range!\n";
        exit(0);
    }
#endif
    Edge ans = source1;

    /* -------------------------------------------------------------------------------------------------
    * Base case 1: constant initial set or constant zero relation
    * ------------------------------------------------------------------------------------------------*/
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\tchecking base case 1\n";
#endif
    if (source1.isConstantZero() || source1.isConstantOne()
        || (source1.isConstantOmega() && source1.getValue() == Value(0))
        || (source1.isConstantOmega() && source1.getValue() == Value(1))
        || relations[begin].getEdge().isConstantZero()) {
        ans = source1Forest->normalizeEdge(lvl, ans);
        return ans;
    }
    /* -------------------------------------------------------------------------------------------------
    * Base case 2: constant one relation
    * ------------------------------------------------------------------------------------------------*/
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\tchecking base case 2\n";
#endif
    if (relations[begin].getEdge().isConstantOne()) {
        if (source1Forest->setting.getEncodeMechanism() == TERMINAL) {
            //
            ans.setEdgeHandle(makeTerminal(1));
            ans.setRule(RULE_X);
        } else {
            ans.setEdgeHandle(makeTerminal(SpecialValue::OMEGA));
            ans.setRule(RULE_X);
            ans.setValue(1);
        };
        ans = source1Forest->normalizeEdge(lvl, ans);
        return ans;
    }

    // determine the max top level
    Level k = source1.getNodeLevel();
    Level m = (k < relations[begin].getEdge().getNodeLevel()) ? relations[begin].getEdge().getNodeLevel() : k;

    /* check in the cache */
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\tchecking cache\n";
#endif
    if (caches[0].check(lvl, source1, ans)) return ans;
    // ----------------------------------------------------
    /* protect source edge */
    // Edge s = source1;
    // ProtectEdge protectSource(source1Forest, s);
    // // protect edges
    // std::vector<Edge> protectChild;
    // std::vector<Edge> protectRec;
    // ----------------------------------------------------

    std::vector<Edge> child(2);
    /* locate the begin even index for recursive calls */
    int childBegin = indexOfTopLessThan(m);
    child[0] = source1Forest->cofact(m, source1, 0);
    child[1] = source1Forest->cofact(m, source1, 1);
    if (childBegin != -1) {
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\tsaturate children\n";
#endif
        /* saturate child edges if there are still events left */
        child[0] = computeSaturation(m-1, child[0], (size_t)childBegin);
        // protectChild.push_back(child[0]);
        // source1Forest->registerEdge(child[0]);

        child[1] = computeSaturation(m-1, child[1], (size_t)childBegin);
        // protectChild.push_back(child[1]);
        // source1Forest->registerEdge(child[1]);
    }
    /* fire all relation s.t. its top level is m */
    // find all such relations
    std::vector<Func> fires;
    std::copy_if(relations.begin(), relations.end(), std::back_inserter(fires),
                [m](Func& a) {
                    return (a.getEdge().getNodeLevel() == m); // assuming there is only long edge rule I0
                });
    if (fires.size() > 0) {
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\tfiring\n";
#endif
        size_t nextBegin = fires.size() + begin;
        // Union of BDDs operation required
        BinaryOperationType unionType = BinaryOperationType::BOP_UNION;
        if (source1Forest->setting.getEncodeMechanism() != TERMINAL) unionType = BinaryOperationType::BOP_MAXIMUM;
        BinaryOperation* un = BOPs.find(unionType, source1Forest, source1Forest, source1Forest);
        if (!un) {
            un = BOPs.add(new BinaryOperation(unionType, source1Forest, source1Forest, source1Forest));
        }
#ifdef BRAVE_DD_SAT_STRATEGY_1
        // child edges firing enough
        bool must0 = !(child[0].isConstantZero() || (child[0].isConstantOmega() && (child[0].getValue() == Value(0))));
        bool must1 = !(child[1].isConstantZero() || (child[1].isConstantOmega() && (child[1].getValue() == Value(0))));
        while (must0 || must1) {
            Edge oldChild, rel, res;
            bool isChanged = 1;
            if (must0) {
                isChanged = 1;
                // Step 1: keep firing 0 edge
                while (isChanged) {
                    oldChild = child[0];
                    for (size_t e=0; e<fires.size(); e++) {
                        rel = source2Forest->cofact(m, fires[e].getEdge(), 0);  // alph[0][0]
                        res = computeImageSat(m-1, child[0], rel, nextBegin);
                        // protectRec.push_back(res);
                        // source1Forest->registerEdge(res);
                        // // source1Forest->deregisterEdge(res);
                        child[0] = un->computeElmtWise(m-1, child[0], res);
                        // protectChild.push_back(child[0]);
                        // source1Forest->registerEdge(child[0]);
                    }
                    if (oldChild == child[0]) isChanged = 0;
                }
                must0 = 0;
                // Step 2: firing 1 edge once more
                oldChild = child[1];
                for (size_t e=0; e<fires.size(); e++) {
                    rel = source2Forest->cofact(m, fires[e].getEdge(), 1);      // alph[0][1]
                    res = computeImageSat(m-1, child[0], rel, nextBegin);
                    // protectRec.push_back(res);
                    // source1Forest->registerEdge(res);
                    // // source1Forest->deregisterEdge(res);
                    child[1] = un->computeElmtWise(m-1, child[1], res);
                    // protectChild.push_back(child[1]);
                    // source1Forest->registerEdge(child[1]);
                    // // source1Forest->deregisterEdge(child[1]);
                }
                if (oldChild != child[1]) must1 = 1;
            }
            if (must1) {
                isChanged = 1;
                // Step 3: keep firing 1 edge
                while (isChanged) {
                    oldChild = child[1];
                    for (size_t e=0; e<fires.size(); e++) {
                        rel = source2Forest->cofact(m, fires[e].getEdge(), 3);  // alph[1][1]
                        res = computeImageSat(m-1, child[1], rel, nextBegin);
                        // protectRec.push_back(res);
                        // source1Forest->registerEdge(res);
                        // // source1Forest->deregisterEdge(res);
                        child[1] = un->computeElmtWise(m-1, child[1], res);
                        // protectChild.push_back(child[1]);
                        // source1Forest->registerEdge(child[1]);
                        // // source1Forest->deregisterEdge(child[1]);
                    }
                    if (oldChild == child[1]) isChanged = 0;
                }
                must1 = 0;
                // Step 4: firing 0 edge once more
                oldChild = child[0];
                for (size_t e=0; e<fires.size(); e++) {
                    rel = source2Forest->cofact(m, fires[e].getEdge(), 2);      // alph[1][0]
                    res = computeImageSat(m-1, child[1], rel, nextBegin);
                    // protectRec.push_back(res);
                    // source1Forest->registerEdge(res);
                    // // source1Forest->deregisterEdge(res);
                    child[0] = un->computeElmtWise(m-1, child[0], res);
                    // protectChild.push_back(child[0]);
                    // source1Forest->registerEdge(child[0]);
                    // // source1Forest->deregisterEdge(child[0]);
                }
                if (oldChild != child[0]) must0 = 1;
            }
        }
#endif
#ifdef BRAVE_DD_SAT_STRATEGY_2
        // fire relation until reaching convergence in any order
        for (size_t e=0; e<fires.size(); e++) {
            // firing until reaching convergence, or go back to the first if reaching new states
            while (true) {
                bool isChanged0 = 0, isChanged1 = 0;
                std::vector<Edge> oldChild(2);
                oldChild = child;
                Edge rRec, resRec;
                for (char i=0; i<4; i++) {
                    char s0Idx = (isPre) ? (i&(0x01)) : ((i&(0x01<<1))>>1);
                    char s1Idx = (isPre) ? ((i&(0x01<<1))>>1) : (i&(0x01));
                    rRec = source2Forest->cofact(m, fires[e].getEdge(), i);
                    resRec = computeImageSat(m-1, child[s0Idx], rRec, nextBegin);
                    child[s1Idx] = un->computeElmtWise(m-1, child[s1Idx], resRec);
                }
                isChanged0 = (child[0] != oldChild[0]);
                isChanged1 = (child[1] != oldChild[1]);
                if (e!=0 && (isChanged0 || isChanged1)) {
                    // reset, go back to the first relation
                    e = 0;
                    break;
                } else if (!isChanged0 && !isChanged1) {
                    break;
                }
            }
        }
#endif
    }
    EdgeLabel root = 0;
    packRule(root, RULE_X);
    ans  = source1Forest->reduceEdge(m, root, m, child);
    /* decide the incoming rule to merge */
    EdgeLabel incoming = 0;
    packRule(incoming, source1.getRule());  // be careful!
    ans = source1Forest->mergeEdge(lvl, m, incoming, ans);
    // ------------------------------------------------------------
    // // protect ans
    // ProtectEdge protectAns(source1Forest, ans);
    // // unprotect
    // for (size_t i=0; i<protectChild.size(); i++) {
    //     source1Forest->deregisterEdge(protectChild[i]);
    // }
    // for (size_t i=0; i<protectRec.size(); i++) {
    //     source1Forest->deregisterEdge(protectRec[i]);
    // }
    // ------------------------------------------------------------

    /* add cache */
    cacheAdd(0, lvl, source1, ans);
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\tafter saturation, ans: ";
    ans.print(std::cout);
    std::cout << std::endl;
#endif
    return ans;
}

Edge SaturationOperation::computeSaturationDistance(const Level lvl, const Edge& source1, const size_t begin)
{
    /* the result would go the same forest as source1 */
    // begin event's level should not be higher than lvl
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "computeSaturationDistance: lvl " << lvl << "; ";
    source1.print(std::cout);
    std::cout << "; begin: " << begin << "; ";
    relations[begin].getEdge().print(std::cout);
    std::cout << std::endl;
    if (begin >= relations.size()) {
        std::cout << "out of range!\n";
        exit(0);
    }
#endif
    Edge ans = source1;

    /* -------------------------------------------------------------------------------------------------
    * Base case: constant initial set or constant zero relation
    * ------------------------------------------------------------------------------------------------*/
    if (source1.isConstantZero()
        || source1.isConstantPosInf()
        || (source1.isConstantOmega() && source1.getValue() == Value(0))
        || relations[begin].getEdge().isConstantZero()) {
        ans = source1Forest->normalizeEdge(lvl, ans);
        return ans;
    }

    // determine the max top level
    Level k = source1.getNodeLevel();
    Level m = (k < relations[begin].getEdge().getNodeLevel()) ? relations[begin].getEdge().getNodeLevel() : k;

    /* check in the cache */
    Value originalVal;
    Edge source1Cache = source1;
    if (source1Forest->setting.getEncodeMechanism() != EDGE_PLUSMOD) {
        originalVal = source1.getValue();
        source1Cache.setValue(0);
    }
    if (caches[0].check(lvl, source1Cache, ans)) {
        if (!ans.isConstantPosInf() && !ans.isConstantNegInf()) ans.setValue(originalVal + ans.getValue());
        return ans;
    }
    std::vector<Edge> child(2);
    /* locate the begin even index for recursive calls */
    int childBegin = indexOfTopLessThan(m);
    child[0] = source1Forest->cofact(m, source1Cache, 0);
    child[1] = source1Forest->cofact(m, source1Cache, 1);
    if (childBegin != -1) {
        /* saturate child edges if there are still events left */
        child[0] = computeSaturationDistance(m-1, child[0], (size_t)childBegin);
        child[1] = computeSaturationDistance(m-1, child[1], (size_t)childBegin);
    }
    /* fire all relation s.t. its top level is m */
    // find all such relations
    std::vector<Func> fires;
    std::copy_if(relations.begin(), relations.end(), std::back_inserter(fires),
                [m](Func& a) {
                    return (a.getEdge().getNodeLevel() == m); // assuming there is only long edge rule I0
                });
    if (fires.size() > 0) {
        size_t nextBegin = fires.size() + begin;
        // Union of BDDs operation required
        BinaryOperation* un = BOPs.find(BinaryOperationType::BOP_MINIMUM, source1Forest, source1Forest, source1Forest);
        if (!un) {
            un = BOPs.add(new BinaryOperation(BinaryOperationType::BOP_MINIMUM, source1Forest, source1Forest, source1Forest));
        }
        // Plus 1 operation required
        BinaryOperation* pls = BOPs.find(BinaryOperationType::BOP_PLUS, source1Forest, source1Forest, source1Forest);
        if (!pls) {
            pls = BOPs.add(new BinaryOperation(BinaryOperationType::BOP_PLUS, source1Forest, source1Forest, source1Forest));
        }
        // make constant one edge
        Edge constantOne;
        if (source1Forest->setting.getEncodeMechanism() == TERMINAL) {
            constantOne.setEdgeHandle(makeTerminal(1));
            constantOne.setRule(RULE_X);
        } else {
            constantOne.setEdgeHandle(makeTerminal(SpecialValue::OMEGA));
            constantOne.setRule(RULE_X);
            constantOne.setValue(1);
        }
#ifdef BRAVE_DD_SAT_STRATEGY_1
        // child edges firing enough
        bool must0 = !(child[0].isConstantZero() || (child[0].isConstantOmega() && (child[0].getValue() == Value(0))) || child[0].isConstantPosInf());
        bool must1 = !(child[1].isConstantZero() || (child[1].isConstantOmega() && (child[1].getValue() == Value(0))) || child[1].isConstantPosInf());
        while (must0 || must1) {
            Edge oldChild, rel, res;
            bool isChanged = 1;
            if (must0) {
                isChanged = 1;
                // Step 1: keep firing 0 edge
                while (isChanged) {
                    oldChild = child[0];
                    for (size_t e=0; e<fires.size(); e++) {
                        rel = source2Forest->cofact(m, fires[e].getEdge(), 0);  // alph[0][0]
                        res = computeImageSatDistance(m-1, child[0], rel, nextBegin);
                        res = pls->computeElmtWise(m-1, res, constantOne);  // +1
                        child[0] = un->computeElmtWise(m-1, child[0], res);
                    }
                    if (oldChild == child[0]) isChanged = 0;
                }
                must0 = 0;
                // Step 2: firing 1 edge once more
                oldChild = child[1];
                for (size_t e=0; e<fires.size(); e++) {
                    rel = source2Forest->cofact(m, fires[e].getEdge(), 1);      // alph[0][1]
                    res = computeImageSatDistance(m-1, child[0], rel, nextBegin);
                    res = pls->computeElmtWise(m-1, res, constantOne);  // +1
                    child[1] = un->computeElmtWise(m-1, child[1], res);
                }
                if (oldChild != child[1]) must1 = 1;
            }
            if (must1) {
                isChanged = 1;
                // Step 3: keep firing 1 edge
                while (isChanged) {
                    oldChild = child[1];
                    for (size_t e=0; e<fires.size(); e++) {
                        rel = source2Forest->cofact(m, fires[e].getEdge(), 3);  // alph[1][1]
                        res = computeImageSatDistance(m-1, child[1], rel, nextBegin);
                        res = pls->computeElmtWise(m-1, res, constantOne);  // +1
                        child[1] = un->computeElmtWise(m-1, child[1], res);
                    }
                    if (oldChild == child[1]) isChanged = 0;
                }
                must1 = 0;
                // Step 4: firing 0 edge once more
                oldChild = child[0];
                for (size_t e=0; e<fires.size(); e++) {
                    rel = source2Forest->cofact(m, fires[e].getEdge(), 2);      // alph[1][0]
                    res = computeImageSatDistance(m-1, child[1], rel, nextBegin);
                    res = pls->computeElmtWise(m-1, res, constantOne);  // +1
                    child[0] = un->computeElmtWise(m-1, child[0], res);
                }
                if (oldChild != child[0]) must0 = 1;
            }
        }
#endif
#ifdef BRAVE_DD_SAT_STRATEGY_2
        // fire relation until reaching convergence in any order
        for (size_t e=0; e<fires.size(); e++) {
            // firing until reaching convergence, or go back to the first if reaching new states
            while (true) {
                bool isChanged0 = 0, isChanged1 = 0;
                std::vector<Edge> oldChild(2);
                oldChild = child;
                Edge rRec, resRec;
                for (char i=0; i<4; i++) {
                    char s0Idx = (isPre) ? (i&(0x01)) : ((i&(0x01<<1))>>1);
                    char s1Idx = (isPre) ? ((i&(0x01<<1))>>1) : (i&(0x01));
                    rRec = source2Forest->cofact(m, fires[e].getEdge(), i);
                    resRec = computeImageSat(m-1, child[s0Idx], rRec, nextBegin);
                    child[s1Idx] = un->computeElmtWise(m-1, child[s1Idx], resRec);
                }
                isChanged0 = (child[0] != oldChild[0]);
                isChanged1 = (child[1] != oldChild[1]);
                if (e!=0 && (isChanged0 || isChanged1)) {
                    // reset, go back to the first relation
                    e = 0;
                    break;
                } else if (!isChanged0 && !isChanged1) {
                    break;
                }
            }
        }
#endif
    }
    EdgeLabel root = 0;
    packRule(root, RULE_X);
    ans  = source1Forest->reduceEdge(m, root, m, child);
    /* decide the incoming rule to merge */
    EdgeLabel incoming = 0;
    packRule(incoming, source1.getRule());  // be careful!
    ans = source1Forest->mergeEdge(lvl, m, incoming, ans);
    cacheAdd(0, lvl, source1Cache, ans);

    if (!ans.isConstantPosInf() && !ans.isConstantNegInf()) ans.setValue(originalVal + ans.getValue());
    return ans;
}

Edge SaturationOperation::computeImageSat(const Level lvl, const Edge& source1, const Edge& trans, const size_t begin)
{
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << ((isPre)?"Pre":"Post") << "ImageSat: lvl: " << (Level)lvl << "; s: ";
    source1.print(std::cout);
    std::cout << "; r: ";
    trans.print(std::cout);
    std::cout << std::endl;
#endif

    Edge ans;
    Edge s, r;
    // normalize edges
    s = source1Forest->normalizeEdge(lvl, source1);
    r = source2Forest->normalizeEdge(lvl, trans);

    // setting info
    EncodeMechanism em = source1Forest->setting.getEncodeMechanism();

    /* -------------------------------------------------------------------------------------------------
    * Base case 1: empty state or relation
    * ------------------------------------------------------------------------------------------------*/
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\tchecking base case 1\n";
#endif
    if (s.isConstantZero()
        || (s.isConstantOmega() && (s.getValue() == Value(0)))
        || r.isConstantZero()) {
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\t\tbase case 1\n";
#endif
        if (em == TERMINAL) {
            EdgeHandle constant = makeTerminal(INT, 0);
            if (source1Forest->getSetting().getValType() == FLOAT) {
                constant = makeTerminal(FLOAT, 0.0f);
            }
            packRule(constant, RULE_X);
            ans.setEdgeHandle(constant);
        } else {
            EdgeHandle constant = makeTerminal(VOID, SpecialValue::OMEGA);
            packRule(constant, RULE_X);
            ans.setEdgeHandle(constant);
        }
        ans = source1Forest->normalizeEdge(lvl, ans);
        return ans;
    }

    /* -------------------------------------------------------------------------------------------------
    * Base case 2: identity or redundant relation
    * ------------------------------------------------------------------------------------------------*/
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\tchecking base case 2\n";
#endif
    if (r.getNodeLevel() == 0) {
        if ((r.getRule() == RULE_I0)
            && (isTerminalOne(r.getEdgeHandle()) || isTerminalZero(r.getEdgeHandle()))
            && (r.getComp() ^ isTerminalOne(r.getEdgeHandle()))) {
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\t\tbase case 2: identity\n";
#endif
            return s;
        } else if (r.isConstantOne()) {
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\t\tbase case 2: redundant\n";
#endif
            if (em == TERMINAL) {
                EdgeHandle constant = makeTerminal(INT, 1);
                if (source1Forest->getSetting().getValType() == FLOAT) {
                    constant = makeTerminal(FLOAT, 1.0f);
                }
                packRule(constant, RULE_X);
                ans.setEdgeHandle(constant);
            } else {
                EdgeHandle constant = makeTerminal(VOID, SpecialValue::OMEGA);
                packRule(constant, RULE_X);
                ans.setEdgeHandle(constant);
                ans.setValue(1);
            }
            ans = source1Forest->normalizeEdge(lvl, ans);
            return ans;
        }
    }

    Level m = (s.getNodeLevel() > r.getNodeLevel()) ? s.getNodeLevel() : r.getNodeLevel();

    /* -------------------------------------------------------------------------------------------------
    * Check cache
    * ------------------------------------------------------------------------------------------------*/
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\tchecking cache\n";
#endif
    // // protect edge
    // ProtectEdge protectS(source1Forest, s);
    if (!caches[1].check(lvl, s, r, ans)) {
        // ------------------------------------------------
        // // protect edges
        // std::vector<Edge> protectChild;
        // std::vector<Edge> protectRec;
        // ------------------------------------------------
        // not cached, computing needed
        std::vector<Edge> child(2);
        EdgeHandle constant = makeTerminal(INT, 0);
        if (source1Forest->getSetting().getValType() == FLOAT) {
            constant = makeTerminal(FLOAT, 0.0f);
        }
        if (em != TERMINAL) {
            constant = makeTerminal(VOID, SpecialValue::OMEGA);
        }
        packRule(constant, RULE_X);
        for (size_t i=0; i<2; i++) {
            child[i].setEdgeHandle(constant);
            child[i] = source1Forest->normalizeEdge(m-1, child[i]);
        }
        int nextId = indexOfTopLessThan(m);
        size_t nextBegin = (nextId == -1) ? relations.size() : (size_t)nextId;
        if ((m > r.getNodeLevel()) && (r.getRule() == RULE_I0)) {
            Edge rr = r;
            if (m-r.getNodeLevel() == 1) rr.setRule(RULE_X);
            child[0] = computeImageSat(m-1, source1Forest->cofact(m, s, 0), rr, nextBegin);
            // protectChild.push_back(child[0]);
            // source1Forest->registerEdge(child[0]);
            child[1] = computeImageSat(m-1, source1Forest->cofact(m, s, 1), rr, nextBegin);
            // protectChild.push_back(child[1]);
            // source1Forest->registerEdge(child[1]);
        } else {
            // recursive computing
            Edge sRec, rRec, resRec;
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\trecursive computing\n";
#endif
            // Union of BDDs operation required
            BinaryOperationType unionType = BinaryOperationType::BOP_UNION;
            if (source1Forest->setting.getEncodeMechanism() != TERMINAL) unionType = BinaryOperationType::BOP_MAXIMUM;
            BinaryOperation* un = BOPs.find(unionType, source1Forest, source1Forest, source1Forest);
            if (!un) {
                un = BOPs.add(new BinaryOperation(unionType, source1Forest, source1Forest, source1Forest));
            }
            for (char i=0; i<4; i++) {
                // if ((r.getRule() == RULE_I0) && (s.getNodeLevel() > m) && (i == 1 || i == 2)) continue;
                char s0Idx = (isPre) ? (i&(0x01)) : ((i&(0x01<<1))>>1);
                char s1Idx = (isPre) ? ((i&(0x01<<1))>>1) : (i&(0x01));
                sRec = source1Forest->cofact(m, s, s0Idx);
                rRec = source2Forest->cofact(m, r, i);
                resRec = computeImageSat(m-1, sRec, rRec, nextBegin);
                // std::cout << "next union in imageSat\n";
                // protectRec.push_back(resRec);
                // source1Forest->registerEdge(resRec);
                child[s1Idx] = un->computeElmtWise(m-1, child[s1Idx], resRec);
                // protect child edges
                // protectChild.push_back(child[s1Idx]);
                // source1Forest->registerEdge(child[s1Idx]);
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\t\tafter union child[" << (int)s1Idx << "]: ";
    child[s1Idx].print(std::cout);
    std::cout << std::endl;
#endif
            }
        }
        EdgeLabel root = 0;
        packRule(root, RULE_X);
        ans = source1Forest->reduceEdge(m, root, m, child);
        // merge with the incoming edge rule
        EdgeLabel incoming = 0;
        packRule(incoming, (r.getRule() == RULE_I0)?s.getRule():RULE_X);    // TBD for rex
        ans = source1Forest->mergeEdge(lvl, m, incoming, ans);
        // saturate before cache
        if (begin < relations.size() ) {
#ifdef BRAVE_DD_OPERATION_TRACE
            std::cout << "\tsaturation before cache\n";
#endif
            ans = computeSaturation(lvl, ans, begin);
        }
        // ---------------------------------------------------------------
        // ProtectEdge protectAns(source1Forest, ans);
        // // unprotect edges
        // for (size_t i=0; i<protectChild.size(); i++) {
        //     source1Forest->deregisterEdge(protectChild[i]);
        // }
        // for (size_t i=0; i<protectRec.size(); i++) {
        //     source1Forest->deregisterEdge(protectRec[i]);
        // }
        // ---------------------------------------------------------------
        // cache
        cacheAdd(1, lvl, s, r, ans);
    }
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "\tafter imageSat at level: " << lvl << ", ans: ";
    ans.print(std::cout);
    std::cout << std::endl;
#endif
    return ans;
}

Edge SaturationOperation::computeImageSatDistance(const Level lvl, const Edge& source1, const Edge& trans, const size_t begin)
{
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << ((isPre)?"Pre":"Post") << "ImageSatDistance: lvl: " << (Level)lvl << "; s: ";
    source1.print(std::cout);
    std::cout << "; r: ";
    trans.print(std::cout);
    std::cout << std::endl;
#endif

    Edge ans;
    Edge s, r;
    // normalize edges
    s = source1Forest->normalizeEdge(lvl, source1);
    r = source2Forest->normalizeEdge(lvl, trans);

    /* -------------------------------------------------------------------------------------------------
    * Base case 1: empty state (INF) or relation (Zero)
    * ------------------------------------------------------------------------------------------------*/
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "checking base case 1\n";
#endif
    if (s.isConstantPosInf() || r.isConstantZero()) {
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "base case 1\n";
#endif
        EdgeHandle constant = makeTerminal(VOID, SpecialValue::POS_INF);
        packRule(constant, RULE_X);
        ans.setEdgeHandle(constant);
        ans = source1Forest->normalizeEdge(lvl, ans);
        return ans;
    }

    /* -------------------------------------------------------------------------------------------------
    * Base case 2: identity or redundant relation
    * ------------------------------------------------------------------------------------------------*/
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "checking base case 2\n";
#endif
    if (r.getNodeLevel() == 0) {
        if ((r.getRule() == RULE_I0) 
            && (isTerminalOne(r.getEdgeHandle()) || isTerminalZero(r.getEdgeHandle()))
            && (r.getComp() ^ isTerminalOne(r.getEdgeHandle()))) {
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "base case 2: identity\n";
#endif
            return s;
        } else if (r.isConstantOne()) {
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "base case 2: redundant\n";
#endif
            // optimization TBD
            if ((source1Forest->setting.getEncodeMechanism() == TERMINAL) && (isTerminal(s.getEdgeHandle()))) {
                EdgeHandle constant = makeTerminal(getTerminalValue(s.getEdgeHandle()));
                packRule(constant, RULE_X);
                ans.setEdgeHandle(constant);
                ans = source1Forest->normalizeEdge(lvl, ans);
                return ans;
            } else if (source1Forest->setting.getEncodeMechanism() != TERMINAL) {
                EdgeHandle constant = makeTerminal(VOID, SpecialValue::OMEGA);
                packRule(constant, RULE_X);
                ans.setEdgeHandle(constant);
                ans.setValue(s.getValue());
                ans = source1Forest->normalizeEdge(lvl, ans);
                return ans;
            }
        }
    }

    Level m = (s.getNodeLevel() > r.getNodeLevel()) ? s.getNodeLevel() : r.getNodeLevel();

    /* -------------------------------------------------------------------------------------------------
    * Check cache
    * ------------------------------------------------------------------------------------------------*/
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "checking cache\n";
#endif
    Value originalVal;
    if (source1Forest->setting.getEncodeMechanism() != EDGE_PLUSMOD) {
        originalVal = s.getValue();
        s.setValue(0);
    }
    if (!caches[1].check(lvl, s, r, ans)) {
        // not cached, computing needed
        std::vector<Edge> child(2);
        EdgeHandle constant = makeTerminal(VOID, SpecialValue::POS_INF);
        packRule(constant, RULE_X);
        for (size_t i=0; i<2; i++) {
            child[i].setEdgeHandle(constant);
            child[i] = source1Forest->normalizeEdge(m-1, child[i]);
        }
        int nextId = indexOfTopLessThan(m);
        size_t nextBegin = (nextId == -1) ? relations.size() : (size_t)nextId;
        if ((m > r.getNodeLevel()) && (r.getRule() == RULE_I0)) {
            Edge rr = r;
            if (m-r.getNodeLevel() == 1) rr.setRule(RULE_X);
            child[0] = computeImageSatDistance(m-1, source1Forest->cofact(m, s, 0), rr, nextBegin);
            child[1] = computeImageSatDistance(m-1, source1Forest->cofact(m, s, 1), rr, nextBegin);
        } else {
            // recursive computing
            Edge sRec, rRec, resRec;
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "recursive computing\n";
#endif
            // Minimum of BDDs operation required
            BinaryOperation* un = BOPs.find(BinaryOperationType::BOP_MINIMUM, source1Forest, source1Forest, source1Forest);
            if (!un) {
                un = BOPs.add(new BinaryOperation(BinaryOperationType::BOP_MINIMUM, source1Forest, source1Forest, source1Forest));
            }
            for (char i=0; i<4; i++) {
                // if ((r.getRule() == RULE_I0) && (s.getNodeLevel() > m) && (i == 1 || i == 2)) continue;
                char s0Idx = (isPre) ? (i&(0x01)) : ((i&(0x01<<1))>>1);
                char s1Idx = (isPre) ? ((i&(0x01<<1))>>1) : (i&(0x01));
                sRec = source1Forest->cofact(m, s, s0Idx);
                rRec = source2Forest->cofact(m, r, i);
                resRec = computeImageSatDistance(m-1, sRec, rRec, nextBegin);
                child[s1Idx] = un->computeElmtWise(m-1, child[s1Idx], resRec);
#ifdef BRAVE_DD_OPERATION_TRACE
    std::cout << "after Minimum child[" << (int)s1Idx << "]: ";
    child[s1Idx].print(std::cout);
    std::cout << std::endl;
#endif
            }
        }
        EdgeLabel root = 0;
        packRule(root, RULE_X);
        ans = source1Forest->reduceEdge(m, root, m, child);
        // merge with the incoming edge rule
        EdgeLabel incoming = 0;
        packRule(incoming, (r.getRule() == RULE_I0)?s.getRule():RULE_X);    // TBD for rex
        ans = source1Forest->mergeEdge(lvl, m, incoming, ans);
        // saturate before cache
        if (begin < relations.size() ) ans = computeSaturationDistance(lvl, ans, begin);
        // cache
        cacheAdd(1, lvl, s, r, ans);
    }
    if (!ans.isConstantPosInf() && !ans.isConstantNegInf()) ans.setValue(originalVal + ans.getValue());
    return ans;
}

void SaturationOperation::sortRelations()
{
    // Assuming the I1 rule, complement, and swap flags are not included
    std::sort(relations.begin(), relations.end(), [](const Func& a, const Func& b) {
        // sorting logic
        Edge ae = a.getEdge(), be = b.getEdge();
        bool aIsTop = (ae.getNodeLevel() == a.getForest()->getSetting().getNumVars());
        bool bIsTop = (be.getNodeLevel() == b.getForest()->getSetting().getNumVars());
        if (aIsTop && bIsTop) {
            return ae.getNodeHandle() < be.getNodeHandle();
        } else if (aIsTop) {
            return true;
        } else if (bIsTop) {
            return false;
        } else {
            if (ae.getRule() != be.getRule()) {
                return ae.getRule() < be.getRule();
            } else if (ae.getNodeLevel() != be.getNodeLevel()) {
                return ae.getNodeLevel() > be.getNodeLevel();
            } else {
                return ae.getNodeHandle() > be.getNodeHandle();
            }
        }
    });
}

int SaturationOperation::indexOfTopLessThan(const Level k)
{
    int ans = -1;
    auto it = std::find_if(relations.begin(), relations.end(), [k](Func& rel) {
        return rel.getEdge().getNodeLevel() < k;
    });
    if (it != relations.end()) {
        ans = static_cast<int>(std::distance(relations.begin(), it));
    }
    return ans;
}

// ******************************************************************
// *                                                                *
// *                    SaturationList  methods                     *
// *                                                                *
// ******************************************************************
SaturationList::SaturationList(const std::string n)
{
    reset(n);
}

SaturationOperation* SaturationList::mtfSaturation(const Forest* source1F, const Forest* source2F, const Forest* resF)
{
    SaturationOperation* prev = front;
    SaturationOperation* curr = front->next;
    while (curr) {
        if ((curr->source1Forest == source1F) && (curr->source2Forest == source2F) && (curr->resForest == resF)) {
            // Move to front
            prev->next = curr->next;
            curr->next = front;
            front = curr;
            return curr;
        }
        prev = curr;
        curr = curr->next;
    }
    return nullptr;
}

void SaturationList::searchRemove(SaturationOperation* bop)
{
    if (!front) return;
    SaturationOperation* prev = front;
    SaturationOperation* curr = front->next;
    while (curr) {
        if (curr == bop) {
            prev->next = curr->next;
            delete curr;
            return;
        }
        prev = curr;
        curr = curr->next;
    }
}

void SaturationList::searchRemove(Forest* forest)
{
    if (!front) return;
    // check front first
    while (front && ((front->source1Forest == forest) || (front->source2Forest == forest) || (front->resForest == forest))) {
        SaturationOperation* toRemove = front;
        front = front->next;
        delete toRemove;
    }
    // check the remaining
    SaturationOperation* curr = front;
    while (curr && curr->next) {
        if ((curr->next->source1Forest == forest) || (curr->next->source2Forest == forest) || (curr->next->resForest == forest)) {
            SaturationOperation* toRemove = curr->next;
            curr->next = curr->next->next;
            delete toRemove;
        } else {
            curr = curr->next;
        }
    }
}

void SaturationList::searchSweepCache(Forest* forest)
{
    if (!front || !forest) return;
    SaturationOperation* curr = front;
    bool isSource1 = curr->source1Forest == forest;
    bool isSource2 = curr->source2Forest == forest;
    bool isRes = curr->resForest == forest;
    while (curr) {
        if (isSource1 || isSource2 || isRes) {
            // sweep cache
            if (isSource1) {
                curr->caches[0].sweep(forest, 0);
                curr->caches[0].sweep(forest, 1);
                curr->caches[1].sweep(forest, 0);
                curr->caches[1].sweep(forest, 1);
            }
            if (isSource2) {
                curr->caches[1].sweep(forest, 2);
            }
        }
        curr = curr->next;
        if (curr) {
            isSource1 = curr->source1Forest == forest;
            isSource2 = curr->source2Forest == forest;
            isRes = curr->resForest == forest;
        }
    }
}

void SaturationList::reportCacheStat(std::ostream& out, int format) const
{
    SaturationOperation* curr = front;
    uint64_t n = 0;
    out << "SaturationList:\n";
    while (curr) {
        out << "CT " << n << " =============================\n";
        out << "Source1 Forest: " << curr->source1Forest->getSetting().getName() << "\n";
        out << "Source2 Forest: " << curr->source2Forest->getSetting().getName() << "\n";
        out << "Result Forest: " << curr->resForest->getSetting().getName() << "\n";
        out << "----------------------------------\n";
        curr->caches[0].reportStat(out, format);
        curr->caches[1].reportStat(out, format);
        curr = curr->next;
        n++;
    }
}
