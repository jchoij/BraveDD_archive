#include "forest.h"
#include "operations/operation.h"

// #define BRAVE_DD_FOREST_TRACE

using namespace BRAVE_DD;
// ******************************************************************
// *                                                                *
// *                                                                *
// *                        Forest methods                          *
// *                                                                *
// *                                                                *
// ******************************************************************

Forest::Forest(const ForestSetting& s):setting(s)
{
    /* Check consistency */
    checkCompatibility();
    nodeSize = setting.nodeSize();
    nodeMan = new NodeManager(this);
    uniqueTable = new UniqueTable(this);
    stats = new Statistics();
}
Forest::~Forest()
{
    delete nodeMan;
    delete uniqueTable;
    delete stats;
    // find and remove all related operations
    UOPs.remove(this);
    BOPs.remove(this);
}
/***************************** Cardinality **********************/
uint64_t Forest::count(Func func, int val)
{
    uint64_t num = 0;
    // TBD
    return num;
}
/****************************** I/O *****************************/
void Forest::exportForest(std::ostream& out)
{
    //
}
void Forest::importForest(std::istream& in)
{
    //
}
/************************* Reduction ****************************/
Edge Forest::normalizeNode(const Level nodeLevel, const std::vector<Edge>& down)
{
    // assuming all child edges are reduced and legal
    /* copy the child info */
    std::vector<Edge> child = down;
#ifdef BRAVE_DD_FOREST_TRACE
    std::cout<<"normalize node:\n";
    child[0].print(std::cout);
    std::cout << std::endl;
    child[1].print(std::cout);
    std::cout << std::endl;
#endif
    /* the result */
    Edge ans;
    ans.setLevel(nodeLevel);
    ans.setRule(RULE_X);    // short
    Node node(setting);
    bool comp = 0, swap = 0, swapTo = 0;
    EncodeMechanism em = setting.getEncodeMechanism();
    /* =================================================================================================
    * BDD for "Set" (Terminal encoding)
    * ================================================================================================*/
    if (!setting.isRelation() && (em == TERMINAL)) {
        if (setting.getSwapType() == ONE) {
            // swap-one logic
            if (child[0].getNodeLevel() != child[1].getNodeLevel()) {
                swap = child[0].getNodeLevel() > child[1].getNodeLevel();
            } else if (child[0].getNodeHandle() != child[1].getNodeHandle()) {
                swap = child[0].getNodeHandle() > child[1].getNodeHandle();
            } else if (child[0].getSwap(0) != child[1].getSwap(0)) {
                swap = child[0].getSwap(0) > child[1].getSwap(0);
            } else {
                ReductionRule rule0 = child[0].getRule(), rule1 = child[1].getRule();
                rule0 = (child[0].getComp())?compRule(rule0):rule0;
                rule1 = (child[1].getComp())?compRule(rule1):rule1;
                swap = rule0 > rule1;
            }
            if (swap) SWAP(child[0], child[1]);
        } else if (setting.getSwapType() == ALL) {
            // swap-all logic
            if (child[0].getNodeLevel() != child[1].getNodeLevel()) {
                swap = child[0].getNodeLevel() > child[1].getNodeLevel();
            } else if (child[0].getNodeHandle() != child[1].getNodeHandle()) {
                swap = child[0].getNodeHandle() > child[1].getNodeHandle();
            } else if (child[0].getSwap(0) == child[1].getSwap(0)) {
                swap = child[0].getSwap(0);
            } else {
                ReductionRule rule0 = child[0].getRule(), rule1 = swapRule(child[1].getRule());
                rule0 = (child[0].getComp())?compRule(rule0):rule0;
                rule1 = (child[1].getComp())?compRule(rule1):rule1;
                swap = rule0 > rule1;
            }
            if (swap) {
                child[0].swap();
                child[1].swap();
                SWAP(child[0], child[1]);
                // check if the swap-all bit 1 necessary, since it may be directly deleted or the same as complement
                char useless0 = 0, useless1 = 0;
                useless0 = isSwapAllUseless(child[0]);
                useless1 = isSwapAllUseless(child[1]);
                if (useless0 == 1) child[0].setSwap(0, 0);
                if (useless1 == 1) child[1].setSwap(0, 0);
                if ((useless0 == 2) && (setting.getCompType() == COMP)) {
                    child[0].setSwap(0, 0);
                    child[0].setComp(!child[0].getComp());
                }
                if ((useless1 == 2) && (setting.getCompType() == COMP)) {
                    child[1].setSwap(0, 0);
                    child[1].setComp(!child[1].getComp());
                }
            }
        }
        comp = child[0].getComp();
        if (comp) {
            child[0].complement();
            child[1].complement();
        }
#ifdef BRAVE_DD_FOREST_TRACE
        std::cout << "normalized child:\n";
        child[0].print(std::cout);
        std::cout << std::endl;
        child[1].print(std::cout);
        std::cout << std::endl;
#endif

        bool hasLvl = setting.getReductionSize() > 0;
        node.setChildEdge(0, child[0].getEdgeHandle(), 0, hasLvl);
        node.setChildEdge(1, child[1].getEdgeHandle(), 0, hasLvl);
    /* =================================================================================================
    * BDD for "Set" (Edge value encoding)
    * ================================================================================================*/
    } else if(!setting.isRelation() && em == EDGE_PLUS) {
        // swap logic
        if (setting.getSwapType() == ONE) {
            // swap-one
            if (child[0].getNodeLevel() != child[1].getNodeLevel()) {
                swap = child[0].getNodeLevel() > child[1].getNodeLevel();
            } else if (child[0].getNodeHandle() != child[1].getNodeHandle()) {
                swap = child[0].getNodeHandle() > child[1].getNodeHandle();
            } else if (child[0].getSwap(0) != child[1].getSwap(0)) {
                swap = child[0].getSwap(0) > child[1].getSwap(0);
            } else {
                ReductionRule rule0 = child[0].getRule(), rule1 = child[1].getRule();
                rule0 = (child[0].getComp())?compRule(rule0):rule0;
                rule1 = (child[1].getComp())?compRule(rule1):rule1;
                swap = rule0 > rule1;
            }
            if (swap) SWAP(child[0], child[1]);
        } else if (setting.getSwapType() == ALL) {
            // swap-all
        }
        bool hasLvl = setting.getReductionSize() > 0;
        /* 
         * One is special terminal value, or both but different, check this first
         */
        EdgeHandle child0 = child[0].getEdgeHandle();
        EdgeHandle child1 = child[1].getEdgeHandle();
        node.setChildEdge(0, child0, 0, hasLvl);
        node.setChildEdge(1, child1, 0, hasLvl);
        // 0 edge is terminal INF
        if (isTerminalSpecial(SpecialValue::POS_INF, child0)
            || isTerminalSpecial(SpecialValue::NEG_INF, child0)
            || isTerminalSpecial(SpecialValue::UNDEF, child0)) {
            if (!isTerminalSpecial(child1) || isTerminalSpecial(SpecialValue::OMEGA, child1)) { 
                ans.setValue(child[1].getValue());
            }
        // 1 edge is terminal INF
        } else if (isTerminalSpecial(SpecialValue::POS_INF, child1)
                || isTerminalSpecial(SpecialValue::NEG_INF, child1)
                || isTerminalSpecial(SpecialValue::UNDEF, child1)) {
            // here 0 child must be Omega terminal or nonterminal
            ans.setValue(child[0].getValue());
        } else {
            if (setting.getValType() == INT) {
                int ev0, ev1, min;
                Value normalized;
                child[0].getValue().getValueTo(&ev0, INT);
                child[1].getValue().getValueTo(&ev1, INT);
                // normalize then mode
                if (ev0 < ev1) {
                    min = ev0;
                    normalized = (ev1 - ev0);
                    node.setEdgeValue(1, normalized);
                } else {
                    min = ev1;
                    normalized = (ev0 - ev1);
                    node.setEdgeValue(0, normalized);
                }
                ans.setValue(min);
            } else if (setting.getValType() == LONG) {
                long ev0, ev1, min;
                Value normalized;
                child[0].getValue().getValueTo(&ev0, LONG);
                child[1].getValue().getValueTo(&ev1, LONG);
                if (ev0 < ev1) {
                    min = ev0;
                    normalized = (ev1 - ev0);
                    node.setEdgeValue(1, normalized);
                } else {
                    min = ev1;
                    normalized = ev0 - ev1;
                    node.setEdgeValue(0, normalized);
                }
                ans.setValue(Value(min));
            } else if (setting.getValType() == FLOAT) {
                //TODO: implement setting values in node
            } else if (setting.getValType() == DOUBLE) {
                //TODO: implement setting values in node
            } else if (setting.getValType() == VOID) {
                // TODO: Talk to Lichuan about this
                // When would be the setting be VOID beside the constant inf func
            }
        }
    /* =================================================================================================
    * BDD for "Set" (Edge value mod encoding)
    * ================================================================================================*/
    } else if (!setting.isRelation() && em == EDGE_PLUSMOD) {
        bool hasLvl = setting.getReductionSize() > 0;
        unsigned long maxRange = (em == EDGE_PLUS) ? 0 : setting.getMaxRange();
        /* 
         * One is special terminal value, or both but different, check this first
         */
        EdgeHandle child0 = child[0].getEdgeHandle();
        EdgeHandle child1 = child[1].getEdgeHandle();
        node.setChildEdge(0, child0, 0, hasLvl);
        node.setChildEdge(1, child1, 0, hasLvl);

        if (setting.getValType() == INT 
            && (maxRange > static_cast<unsigned long>(std::numeric_limits<int>::max()))) {
                std::cout << "[BRAVE_DD] ERROR!\t maxRange overflows valType specified" << std::endl;
                exit(0);
        }
        if (setting.getValType() == LONG 
            && (maxRange > static_cast<unsigned long>(std::numeric_limits<long>::max()))) {
                std::cout << "[BRAVE_DD] ERROR!\t maxRange overflows valType specified" << std::endl;
                exit(0);
        }

        // 0 edge is terminal INF
        if (isTerminalSpecial(SpecialValue::POS_INF, child0)
            || isTerminalSpecial(SpecialValue::NEG_INF, child0)
            || isTerminalSpecial(SpecialValue::UNDEF, child0)) {
            if (!isTerminalSpecial(child1) || isTerminalSpecial(SpecialValue::OMEGA, child1)) { 
                ans.setValue(child[1].getValue());
            }
        // 1 edge is terminal INF
        } else if (isTerminalSpecial(SpecialValue::POS_INF, child1)
                || isTerminalSpecial(SpecialValue::NEG_INF, child1)
                || isTerminalSpecial(SpecialValue::UNDEF, child1)) {
            // here 0 child must be Omega terminal or nonterminal
            ans.setValue(child[0].getValue());
        } else {
            if (setting.getValType() == INT) {
                int ev0, ev1, mod;
                mod = static_cast<int>(maxRange);
                Value normalized;
                child[0].getValue().getValueTo(&ev0, INT);
                child[1].getValue().getValueTo(&ev1, INT);
                normalized = Value(((((ev1 - ev0) % mod) + mod) % mod));
                node.setEdgeValue(1, normalized);
                ans.setValue(ev0);
            } else if (setting.getValType() == LONG) {
                long ev0, ev1, mod;
                mod = static_cast<long>(maxRange);
                Value normalized;
                child[0].getValue().getValueTo(&ev0, LONG);
                child[1].getValue().getValueTo(&ev1, LONG);
                normalized = Value(((((ev1 - ev0) % mod) + mod) % mod));
                node.setEdgeValue(1, normalized);
                ans.setValue(ev0);
            } else if (setting.getValType() == FLOAT) {
                //TODO: implement setting values in node
            } else if (setting.getValType() == DOUBLE) {
                //TODO: implement setting values in node
            } else if (setting.getValType() == VOID) {
                // TODO: Talk to Lichuan about this
                // When would be the setting be VOID beside the constant inf func
            }
        }    
    /* =================================================================================================
    * BDD for "Relation" (Terminal encoding)
    * ================================================================================================*/
    } else if (setting.isRelation() && em == TERMINAL){
        // for relation BDD TBD
        bool hasLvl = setting.getReductionSize() > 0;
        node.setChildEdge(0, child[0].getEdgeHandle(), 1, hasLvl);
        node.setChildEdge(1, child[1].getEdgeHandle(), 1, hasLvl);
        node.setChildEdge(2, child[2].getEdgeHandle(), 1, hasLvl);
        node.setChildEdge(3, child[3].getEdgeHandle(), 1, hasLvl);
    /* =================================================================================================
    * BDD for "Relation" (Edge value encoding)
    * ================================================================================================*/
    } else if(setting.isRelation() && (em == EDGE_PLUS)) {
    } else {
        // others, TBD
    }
    ans.setComp(comp);
    ans.setSwap(swap, 0);
    ans.setSwap(swapTo, 1);
    ans.setNodeHandle(insertNode(nodeLevel, node));
#ifdef BRAVE_DD_FOREST_TRACE
    std::cout << "normalize done, ans edge: ";
    ans.print(std::cout);
    std::cout << std::endl;
#endif
    return ans;
}

Edge Forest::normalizeEdge(const Level level, const Edge& edge)
{
#ifdef BRAVE_DD_FOREST_TRACE
    std::cout << "normalize edge from level: " << level << "; ";
    edge.print(std::cout);
    std::cout << std::endl;
#endif
    Edge normalized = edge;
    // std::cout << "normalize edge at level : " << level << std::endl;
    // double ev;
    // edge.getValue().getValueTo(&ev, DOUBLE);
    // std::cout << "edge value : "<< ev << std::endl; 
    bool isCompAllowed = (setting.getCompType() != NO_COMP);
    ReductionRule rule = edge.getRule();
    bool comp = edge.getComp();
    Level targetLvl = edge.getNodeLevel();
    
    /* Case 0: short edge to nonterminal node */
    if ((level == targetLvl) && (targetLvl > 0)) {
        normalized.setRule(RULE_X);
        return normalized;
    }
    /* case 1: AL/AH edges but only skip 1 level, normalize it to EL/EH */
    if (level - targetLvl == 1) {
        if ((rule == RULE_AL0) && setting.hasReductionRule(RULE_EL0)) {
            normalized.setRule(RULE_EL0);
        } else if ((rule == RULE_AL1) && setting.hasReductionRule(RULE_EL1)) {
            normalized.setRule(RULE_EL1);
        } else if ((rule == RULE_AH0) && setting.hasReductionRule(RULE_EH0)) {
            normalized.setRule(RULE_EH0);
        } else if ((rule == RULE_AH1) && setting.hasReductionRule(RULE_EH1)) {
            normalized.setRule(RULE_EH1);
        }
    }
    /* Case 2: target to terminal node */
    if (targetLvl == 0) {
        Value termVal = getTerminalValue(edge.handle);
        union {
            int             valInt;
            float           valFloat;
            SpecialValue    valSp;
        };
        // rule 1: forbidding swap flags to terminal node
        normalized.setSwap(0,0);
        normalized.setSwap(0,1);
        // rule 2: forbidding terminal value > N/2, if complement flag allowed
        if (setting.getCompType() != NO_COMP) {
            if (termVal.getType() == INT) {
                termVal.getValueTo(&valInt, INT);
                if ((setting.getMaxRange() - valInt) <= (double)(setting.getMaxRange())/2) {
                    normalized.handle = makeTerminal(INT, setting.getMaxRange() - valInt);
                    normalized.setRule(rule);
                    normalized.setComp(!comp);
                }
            } else if (termVal.getType() == FLOAT) {
                termVal.getValueTo(&valFloat, FLOAT);
                if (valFloat >= (setting.getMaxRange()/2)) {
                    normalized.handle = makeTerminal(FLOAT, setting.getMaxRange() - valInt);
                    normalized.setRule(rule);
                    normalized.setComp(!comp);
                }
            } else if (termVal.getType() == VOID) {
                termVal.getValueTo(&valSp, VOID);
                if ((valSp == SpecialValue::POS_INF) && setting.hasNegInf()) {
                    normalized.handle = makeTerminal(VOID, SpecialValue::NEG_INF);
                    normalized.setRule(rule);
                    normalized.setComp(!comp);
                }
            }
        } else if (comp) {
            // this edge should not have complement flag
            if (termVal.getType() == INT) {
                termVal.getValueTo(&valInt, INT);
                normalized.handle = makeTerminal(INT, setting.getMaxRange() - valInt);
            } else if (termVal.getType() == FLOAT) {
                termVal.getValueTo(&valFloat, FLOAT);
                normalized.handle = makeTerminal(FLOAT, setting.getMaxRange() - valInt);
            } else if (termVal.getType() == VOID) {
                termVal.getValueTo(&valSp, VOID);
                if (valSp == SpecialValue::POS_INF) {
                    if (setting.hasNegInf()) {
                        normalized.handle = makeTerminal(VOID, SpecialValue::NEG_INF);
                    } else {
                        std::cout << "[BRAVE_DD] ERROR!\t Normalize edge: Miss [Neg_Inf] in setting!" << std::endl;
                        exit(0);
                    }
                } else if (valSp == SpecialValue::NEG_INF) {
                    if (setting.hasPosInf()) {
                        normalized.handle = makeTerminal(VOID, SpecialValue::POS_INF);
                    } else {
                        std::cout << "[BRAVE_DD] ERROR!\t Normalize edge: Miss [Pos_Inf] in setting!" << std::endl;
                        exit(0);
                    }
                }
            }
            normalized.setRule(rule);
            normalized.setComp(!comp);
        }
        // rule 3: constant edge, if reduction rule X allowed and target to terminal 0 or 1
        bool isTermOne = isTerminalOne(normalized.handle);
        bool isTermZero = isTerminalZero(normalized.handle);
        if (((rule != RULE_X) && (hasRuleTerminalOne(rule) == (normalized.getComp()^isTermOne)) && (isTermOne || isTermZero))
            || ((rule == RULE_X) && (level - targetLvl > 0))
            || (level - targetLvl == 0)) {
            // it should be a long X anyway
            normalized.setRule(RULE_X);
            if (!setting.hasReductionRule(RULE_X) && (level - targetLvl > 0)) {
                // long X is not allowed, try to find a legal reduction rule
                for (int r=0; r<11; r++){
                    if (setting.hasReductionRule((ReductionRule)r)
                        && ((normalized.getComp()^isTermOne) == hasRuleTerminalOne((ReductionRule)r))) {
                        normalized.setRule((ReductionRule)r);
                        break;
                    }
                }
            }
        }
        // rule 4: EH edge at level 1 target to terminal 0 or 1, changed to EL
        if ((level == 1)
            && isRuleEH(normalized.getRule())
            && (hasRuleTerminalOne(normalized.getRule()) != (normalized.getComp()^isTermOne))
            && (isTermOne || isTermZero)) {
            if ((normalized.getRule() == RULE_EH0) && setting.hasReductionRule(RULE_EL1)) {
                if (termVal.getType() == INT) {
                    normalized.handle = makeTerminal(INT, 0);
                } else {
                    normalized.handle = makeTerminal(FLOAT, 0.0f);
                }
                normalized.setRule(RULE_EL1);
                normalized.setComp(0);
            } else if ((normalized.getRule() == RULE_EH1) && setting.hasReductionRule(RULE_EL0)) {
                if (isCompAllowed) {
                    if (termVal.getType() == INT) {
                        normalized.handle = makeTerminal(INT, 0);
                    } else {
                        normalized.handle = makeTerminal(FLOAT, 0.0f);
                    }
                    normalized.setComp(1);
                } else{
                    if (termVal.getType() == INT) {
                        normalized.handle = makeTerminal(INT, 1);
                    } else {
                        normalized.handle = makeTerminal(FLOAT, 1.0f);
                    }
                    normalized.setComp(0);
                }
                normalized.setRule(RULE_EL0);
            }
        }
    }
    /* Case 3: long edge with reduction rule that is not allowed */
    rule = normalized.getRule();
    comp = normalized.getComp();
    if ((level - targetLvl > 0) && !setting.hasReductionRule(rule)) {
        std::vector<Edge> childEdges;
        if (setting.isRelation()) {
            childEdges = std::vector<Edge>(4);
        } else {
            childEdges = std::vector<Edge>(2);
        }
        Edge temp = normalized;
        if (rule == RULE_X) {
            // it should be built
            for (Level k=targetLvl+1; k<=level; k++) {
                for (size_t i=0; i<childEdges.size(); i++) {
                    childEdges[i] = temp;
                }
                temp = reduceNode(k, childEdges);
            }
        } else if (isRuleEL(rule) || isRuleEH(rule) || isRuleAL(rule) || isRuleAH(rule)) {
            bool child = (isRuleEL(rule) || isRuleAL(rule)) ? 0 : 1;
            childEdges[child].handle = makeTerminal(INT,(int)hasRuleTerminalOne(rule));
            if (setting.getValType() == FLOAT) {
                childEdges[child].handle = makeTerminal(FLOAT,(float)hasRuleTerminalOne(rule));
            }
            childEdges[child].setRule(RULE_X);
            childEdges[!child] = temp;
            childEdges[!child].setRule(RULE_X);
            for (Level k=targetLvl+1; k<=level; k++) {
                childEdges[0] = normalizeEdge(k-1, childEdges[0]);
                childEdges[1] = normalizeEdge(k-1, childEdges[1]);
                temp = reduceNode(k, childEdges);
                childEdges[(isRuleEH(rule) || isRuleAL(rule))?0:1] = temp;
            }
        } else if (isRuleI(rule)) {
            childEdges[0] = temp;
            childEdges[3] = temp;
            childEdges[1].handle = makeTerminal(INT,(int)hasRuleTerminalOne(rule));
            childEdges[1].setRule(RULE_X);
            childEdges[2].handle = makeTerminal(INT,(int)hasRuleTerminalOne(rule));
            childEdges[2].setRule(RULE_X);
            for (Level k=targetLvl+1; k<=level; k++) {
                childEdges[0] = normalizeEdge(k-1, childEdges[0]);
                childEdges[1] = normalizeEdge(k-1, childEdges[1]);
                childEdges[2] = normalizeEdge(k-1, childEdges[2]);
                childEdges[3] = normalizeEdge(k-1, childEdges[3]);
                temp = normalizeNode(k, childEdges);
                childEdges[0] = temp;
                childEdges[3] = temp;
            }
        }
        normalized.setEdgeHandle(temp.getEdgeHandle()); // not change the original edge value
    }

    return normalized;
}

Edge Forest::reduceNode(const Level nodeLevel, const std::vector<Edge>& down)
{
    /* copy the child info , then normalize them */
    std::vector<Edge> child = down;
    for (size_t i=0; i<child.size(); i++) {
        child[i] = normalizeEdge(nodeLevel-1, child[i]);
    }
#ifdef BRAVE_DD_FOREST_TRACE
    std::cout << "reduce node: \n";
    child[0].print(std::cout);
    std::cout << std::endl;
    child[1].print(std::cout);
    std::cout << std::endl;
#endif
    /* setting info */
    bool isCompAllowed = (setting.getCompType() != NO_COMP);
    // bool isSwapAllowed = (setting.getSwapType() != NO_SWAP);
    /* The final answer, initialized */
    Edge reduced;
    if (setting.getValType() == INT || setting.getValType() == LONG) {
        reduced.handle = makeTerminal(INT, 0);
    } else if (setting.getValType() == FLOAT || setting.getValType() == DOUBLE) {
        reduced.handle = makeTerminal(FLOAT, 0.0f);
    } else {
        reduced.handle = makeTerminal(VOID, SpecialValue::OMEGA);
    }
    EncodeMechanism em = setting.getEncodeMechanism();
    /* check if the node matches an illegal pattern */
    /* =================================================================================================
    * BDD for "Set" (Terminal encoding)
    * ================================================================================================*/
    if (!setting.isRelation() && (em == TERMINAL)) {
        if (setting.hasReductionRule(RULE_00)) {
            if (
                    (child[0].getNodeLevel() == child[1].getNodeLevel())
                    && (child[0].getNodeHandle() == child[1].getNodeHandle()) 
                    && (child[0].getComp() == child[1].getComp()) 
                    && (child[0].getSwap(0) == child[1].getSwap(0)) 
                    && (child[0].getRule() == RULE_X && child[1].getRule() == RULE_X)
            ) {
                return child[0];
            }

            if (child[1].getNodeLevel() != 0) {
                if (setting.hasReductionRule(RULE_00))
                {
                    Edge oneZero = getChildEdge(child[1].getNodeLevel(), child[1].getNodeHandle(), child[1].getSwap(0));
                    if(child[1].getComp()) oneZero.complement();
                    bool a1 = ((nodeLevel == child[1].getNodeLevel() + 1) || child[1].getRule() == RULE_00);
                    bool a2 = (child[0].getNodeLevel() == oneZero.getNodeLevel()) && (child[0].getNodeHandle() == oneZero.getNodeHandle());
                    bool a3 = ((child[0].getComp() == oneZero.getComp()) && oneZero.getRule() == child[0].getRule() && child[0].getSwap(0) == oneZero.getSwap(0));
                    if (a1 && a2 && a3)
                    {
                        reduced = child[1];
                        reduced.setRule(RULE_00);
                        return reduced;
                    }
                }        
            }

            if (child[0].getNodeLevel() != 0) {
                if (setting.hasReductionRule(RULE_11))
                {
                    Edge zeroOne = getChildEdge(child[0].getNodeLevel(), child[0].getNodeHandle(), !child[0].getSwap(0));
                    if (child[0].getComp()) zeroOne.complement();
                    bool o1 = ((nodeLevel == child[0].getNodeLevel() + 1) || child[0].getRule() == RULE_11);
                    bool o2 = (child[1].getNodeHandle() == zeroOne.getNodeHandle() && child[1].getNodeLevel() == zeroOne.getNodeLevel());
                    bool o3 = ((child[1].getComp() == zeroOne.getComp()) && zeroOne.getRule() == child[1].getRule() && child[1].getSwap(0) == zeroOne.getSwap(0));
                    if (o1 && o2 && o3)
                    {
                        reduced = child[0];
                        reduced.setRule(RULE_11);
                        return reduced;
                    }
                }
            }
            return normalizeNode(nodeLevel, child);
        }
        // flag for checking if match any allowed meta-reduction rule
        bool isMatch = 0;
        /* ---------------------------------------------------------------------------------------------
        * Forbidden patterns of nodes with both edges to terminals
        * --------------------------------------------------------------------------------------------*/
        if ((child[0].getNodeLevel() == 0) && (child[1].getNodeLevel() == 0)) {
            // flags to identify if terminal 0 or 1
            bool isTermOne0 = isTerminalOne(child[0].getEdgeHandle());
            bool isTermOne1 = isTerminalOne(child[1].getEdgeHandle());
            bool isTermZero0 = isTerminalZero(child[0].getEdgeHandle());
            bool isTermZero1 = isTerminalZero(child[1].getEdgeHandle());
            /* Meta-edge: Constant <C, 0, c, 0/1> */
            if (((child[0].getRule() == RULE_X) || (hasRuleTerminalOne(child[0].getRule()) == (child[0].getComp() ^ isTermOne0)))
                && ((child[1].getRule() == RULE_X) || (hasRuleTerminalOne(child[1].getRule()) == (child[1].getComp() ^ isTermOne1)))
                && ((isTermOne0 || isTermZero0) && (isTermOne1 || isTermZero1))
                && ((child[0].getComp() ^ isTermOne0) == (child[1].getComp() ^ isTermOne1))
                && (nodeLevel >= 1)) {
                if (setting.hasReductionRule(RULE_X)) {
                    reduced = child[0];
                    isMatch = 1;
                } else {
                    // enumerate from EL0 to AH1 to check if it's allowed
                    for (int r=0; r<8; r++){
                        if (setting.hasReductionRule((ReductionRule)r)
                            && ((child[0].getComp()^isTermOne0) == hasRuleTerminalOne((ReductionRule)r))) {
                            reduced = child[0];
                            reduced.setRule((ReductionRule)r);
                            isMatch = 1;
                            break;
                        }
                    }
                }
            /* Meta-edge: Constant <C, 0, c, n>, n>1; complement bit TBD */
            } else if ((child[0].getEdgeHandle() == child[1].getEdgeHandle())
                        && (child[0].getRule() == RULE_X)) {
                reduced = child[0];
                isMatch = 1;
            /* Meta-edge: Bottom variable <B, 0, c, 0> */
            } else if ((child[0].getRule() == RULE_X)
                        && (child[1].getRule() == RULE_X)
                        && (nodeLevel == 1)
                        && ((child[0].getComp()^isTermOne0) != (child[1].getComp()^isTermOne1))
                        && (isTermOne0 || isTermZero0)
                        && (isTermOne1 || isTermZero1)) {
                // enumerate from EL0 to AH1 to check if it's allowed
                for (int r=0; r<8; r++){
                    if (setting.hasReductionRule((ReductionRule)r)
                        && (r < 4)    // EL or AL
                        && ((child[0].getComp()^isTermOne0) == hasRuleTerminalOne((ReductionRule)r))) {
                        reduced = child[1];
                        reduced.setRule((ReductionRule)r);
                        isMatch = 1;
                        break;
                    } else if (setting.hasReductionRule((ReductionRule)r)
                        && (r >= 4)   // EH or AH
                        && ((child[1].getComp()^isTermOne1) == hasRuleTerminalOne((ReductionRule)r))) {
                        reduced = child[0];
                        reduced.setRule((ReductionRule)r);
                        isMatch = 1;
                        break;
                    }
                }
            /* Meta-edge: anD (conjunction) <D, 0, c, 0> */
            } else if (((child[0].getRule() == RULE_X) || (hasRuleTerminalOne(child[0].getRule()) == (child[0].getComp() ^ isTermOne0)))
                        && (child[1].getRule() != RULE_X)
                        && (nodeLevel > 1)
                        && ((((child[0].getComp()^isTermOne0) != (child[1].getComp()^isTermOne1))
                                && isRuleEL(child[1].getRule()))
                            || (((child[0].getComp()^isTermOne0) == (child[1].getComp()^isTermOne1)) 
                                && ((nodeLevel==2 && isRuleEH(child[1].getRule()))
                                    || (nodeLevel>2 && isRuleAH(child[1].getRule())))))
                        && (hasRuleTerminalOne(child[1].getRule()) != (child[1].getComp()^isTermOne1))
                        && (isTermOne0 || isTermZero0)
                        && (isTermOne1 || isTermZero1)) {
                if ((child[0].getComp()^isTermOne0) == 0) {
                    if (setting.hasReductionRule(RULE_EL0)) {
                        if (!isCompAllowed) {
                            // make terminal one
                            if (setting.getValType() == INT || setting.getValType() == LONG) {
                                reduced.handle = makeTerminal(INT, 1);
                            } else if (setting.getValType() == FLOAT || setting.getValType() == DOUBLE) {
                                reduced.handle = makeTerminal(FLOAT, 1.0f);
                            }
                        } else {
                            reduced.setComp(1);
                        }
                        reduced.setRule(RULE_EL0);
                        isMatch = 1;
                    } else if (setting.hasReductionRule(RULE_AH1)) {
                        reduced.setRule(RULE_AH1);
                        isMatch = 1;
                    }
                } else {
                    if (setting.hasReductionRule(RULE_EL1)) {
                        reduced.setRule(RULE_EL1);
                        isMatch = 1;
                    } else if (setting.hasReductionRule(RULE_AH0)) {
                        if (!isCompAllowed) {
                            // make terminal one
                            if (setting.getValType() == INT || setting.getValType() == LONG) {
                                reduced.handle = makeTerminal(INT, 1);
                            } else if (setting.getValType() == FLOAT || setting.getValType() == DOUBLE) {
                                reduced.handle = makeTerminal(FLOAT, 1.0f);
                            }
                        } else {
                            reduced.setComp(1);
                        }
                        reduced.setRule(RULE_AH0);
                        isMatch = 1;
                    }
                }
            /* Meta-edge: oR (disjunction) <R, 0, c, 0> */
            } else if (((child[1].getRule() == RULE_X) || (hasRuleTerminalOne(child[1].getRule()) == (child[1].getComp() ^ isTermOne1)))
                        && (child[0].getRule() != RULE_X)
                        && (nodeLevel > 1)
                        && ((((child[0].getComp()^isTermOne0) != (child[1].getComp()^isTermOne1))
                                && isRuleEH(child[0].getRule()))
                            || (((child[0].getComp()^isTermOne0) == (child[1].getComp()^isTermOne1)) 
                                && ((nodeLevel==2 && (isRuleEL(child[0].getRule())))
                                    || (nodeLevel>2 && isRuleAL(child[0].getRule())))))
                        && (hasRuleTerminalOne(child[0].getRule()) != (child[0].getComp()^isTermOne0))
                        && (isTermOne0 || isTermZero0)
                        && (isTermOne1 || isTermZero1)) {
                if ((child[1].getComp()^isTermOne1) == 0) {
                    if (setting.hasReductionRule(RULE_EH0)) {
                        if (!isCompAllowed) {
                            // make terminal one
                            if (setting.getValType() == INT || setting.getValType() == LONG) {
                                reduced.handle = makeTerminal(INT, 1);
                            } else if (setting.getValType() == FLOAT || setting.getValType() == DOUBLE) {
                                reduced.handle = makeTerminal(FLOAT, 1.0f);
                            }
                        } else {
                            reduced.setComp(1);
                        }
                        reduced.setRule(RULE_EH0);
                        isMatch = 1;
                    } else if (setting.hasReductionRule(RULE_AL1)) {
                        reduced.setRule(RULE_AL1);
                        isMatch = 1;
                    }
                } else {
                    if (setting.hasReductionRule(RULE_EH1)) {
                        reduced.setRule(RULE_EH1);
                        isMatch = 1;
                    } else if (setting.hasReductionRule(RULE_AL0)) {
                        if (!isCompAllowed) {
                            // make terminal one
                            if (setting.getValType() == INT || setting.getValType() == LONG) {
                                reduced.handle = makeTerminal(INT, 1);
                            } else if (setting.getValType() == FLOAT || setting.getValType() == DOUBLE) {
                                reduced.handle = makeTerminal(FLOAT, 1.0f);
                            }
                        } else {
                            reduced.setComp(1);
                        }
                        reduced.setRule(RULE_AL0);
                        isMatch = 1;
                    }
                }
            } else {
                // here means this is not a forbidden node pattern, then normalize and insert node
                return normalizeNode(nodeLevel, child);
            }
        /* ---------------------------------------------------------------------------------------------
        * Forbidden patterns of nodes with Low edge to terminal 0 and High edge to nonterminal
        * --------------------------------------------------------------------------------------------*/
        // Note: Low edge must be a long edge
        } else if ((child[0].getNodeLevel() == 0) && (child[1].getNodeLevel() != 0)) {
            bool isTermOne0 = isTerminalOne(child[0].getEdgeHandle());
            bool isTermZero0 = isTerminalZero(child[0].getEdgeHandle());
            bool comp0 = child[0].getComp();
            ReductionRule rule0 = child[0].getRule();
            ReductionRule rule1 = child[1].getRule();
            if (((rule0 == RULE_X) || (hasRuleTerminalOne(rule0) == (comp0 ^ isTermOne0)))
                && (isTermOne0 || isTermZero0)
                && (((rule1 == RULE_X)
                        && (nodeLevel - child[1].getNodeLevel() == 1)
                        && (setting.hasReductionRule((isTermOne0^comp0)? RULE_EL1 : RULE_EL0)))
                    || (isRuleEL(rule1)
                        && (nodeLevel - child[1].getNodeLevel() > 1)
                        && (hasRuleTerminalOne(rule1) == (isTermOne0^comp0)))) ) {
                    reduced = child[1];
                    reduced.setRule((isTermOne0^comp0)?RULE_EL1:RULE_EL0);
                    isMatch = 1;
            } else {
                // here means this is not a forbidden node pattern, then normalize and insert node
                return normalizeNode(nodeLevel, child);
            }
        /* ---------------------------------------------------------------------------------------------
        * Forbidden patterns of nodes with High edge to terminal 0 and Low edge to nonterminal
        * --------------------------------------------------------------------------------------------*/
        } else if ((child[0].getNodeLevel() != 0) && (child[1].getNodeLevel() == 0)) {
            bool isTermOne1 = isTerminalOne(child[1].getEdgeHandle());
            bool isTermZero1 = isTerminalZero(child[1].getEdgeHandle());
            bool comp1 = child[1].getComp();
            ReductionRule rule0 = child[0].getRule();
            ReductionRule rule1 = child[1].getRule();
            if (((rule1 == RULE_X) || (hasRuleTerminalOne(rule1) == (comp1 ^ isTermOne1)))
                && (isTermOne1 || isTermZero1)
                && (((rule0 == RULE_X)
                        && (nodeLevel - child[0].getNodeLevel() == 1)
                        && (setting.hasReductionRule((isTermOne1^comp1)? RULE_EH1 : RULE_EH0)))
                    || (isRuleEH(rule0)
                        && (nodeLevel - child[0].getNodeLevel() > 1)
                        && (hasRuleTerminalOne(rule0) == (isTermOne1^comp1) )))) {
                    reduced = child[0];
                    reduced.setRule((isTermOne1^comp1)?RULE_EH1:RULE_EH0);
                    isMatch = 1;
            } else {
                // here means this is not a forbidden node pattern, then normalize and insert node
                return normalizeNode(nodeLevel, child);
            }
        /* ---------------------------------------------------------------------------------------------
        * Forbidden patterns of nodes with both edges to the same nonterminal
        * --------------------------------------------------------------------------------------------*/
        } else {
            if ((child[0].getNodeLevel() == child[1].getNodeLevel())
                && (child[0].getNodeHandle() == child[1].getNodeHandle())
                && (child[0].getComp() == child[1].getComp())
                && (child[0].getSwap(0) == child[1].getSwap(0)) ) {
                /* X reduction rule */
                if ((child[0].getRule() == child[1].getRule())
                    && (child[0].getRule() == RULE_X)
                    && setting.hasReductionRule(RULE_X)) {
                    reduced = child[0];
                    isMatch = 1;
                /* AL reduction rule */
                } else if ((child[1].getRule() == RULE_X)
                            && ((isRuleEL(child[0].getRule())
                                    && (nodeLevel - child[0].getNodeLevel() == 1))
                                || (isRuleAL(child[0].getRule())
                                    && (nodeLevel - child[0].getNodeLevel() > 1)))
                            && (setting.hasReductionRule((hasRuleTerminalOne(child[0].getRule())) ? RULE_AL1 : RULE_AL0)) ) {
                    reduced = child[0];
                    reduced.setRule((hasRuleTerminalOne(child[0].getRule())) ? RULE_AL1 : RULE_AL0);
                    isMatch = 1;
                /* AH reduction rule */
                } else if ((child[0].getRule() == RULE_X)
                            && ((isRuleEH(child[1].getRule())
                                    && (nodeLevel - child[1].getNodeLevel() == 1))
                                || (isRuleAH(child[1].getRule())
                                    && (nodeLevel - child[1].getNodeLevel() > 1)))
                            && (setting.hasReductionRule((hasRuleTerminalOne(child[1].getRule())) ? RULE_AH1 : RULE_AH0)) ) {
                    reduced = child[1];
                    reduced.setRule((hasRuleTerminalOne(child[1].getRule())) ? RULE_AH1 : RULE_AH0);
                    isMatch = 1;
                }
            } else {
                // here means this is not a forbidden node pattern, then normalize and insert node
                return normalizeNode(nodeLevel, child);
            }
            
        }
        // here means the forbidden node pattern found but its equivalent edge rules are not allowed
        if (!isMatch) return normalizeNode(nodeLevel, child);

    /* =================================================================================================
    * BDD for "Set" (Edge value encoding)
    * ================================================================================================*/
    } else if (!setting.isRelation() && em == EDGE_PLUS){
        bool isMatch = 0;
        /* ---------------------------------------------------------------------------------------------
        * Redundant X
        * --------------------------------------------------------------------------------------------*/ 
       if ((child[0] == child[1]) && setting.hasReductionRule(RULE_X)) {
            reduced = child[0];
            isMatch = 1;
       }        
        if (!isMatch) return normalizeNode(nodeLevel, child);
    
    } else if (!setting.isRelation() && em == EDGE_PLUSMOD) {
        bool isMatch = 0;
        /* ---------------------------------------------------------------------------------------------
        * Redundant X
        * --------------------------------------------------------------------------------------------*/ 
        unsigned long maxRange = setting.getMaxRange();
        if (setting.getValType() == INT) {
            int ev0, ev1, mod;
            if (maxRange > static_cast<unsigned long>(std::numeric_limits<int>::max())) {
                std::cout << "[BRAVE_DD] ERROR!\t maxRange overflows valType specified" << std::endl;
                exit(0);
            }
            else mod = static_cast<int>(maxRange);
            child[0].getValue().getValueTo(&ev0,INT);
            child[1].getValue().getValueTo(&ev1,INT);
            ev0 = mod ? ev0 % mod : ev0;
            ev1 = mod ? ev1 % mod : ev0;
            if(((child[0].getEdgeHandle() == child[1].getEdgeHandle())
            && (ev0 == ev1)
            && setting.hasReductionRule(RULE_X))) {
            child[0].setValue(ev0 % mod);
            reduced = child[0];
            isMatch = 1;
            }
            
        } else if (setting.getValType() == LONG) {
            long ev0, ev1, mod;
            if (maxRange > static_cast<unsigned long>(std::numeric_limits<long>::max())) {
                std::cout << "[BRAVE_DD] ERROR!\t maxRange overflows valType specified" << std::endl;
                exit(0);
            }
            else mod = static_cast<long>(maxRange);
            child[0].getValue().getValueTo(&ev0,LONG);
            child[1].getValue().getValueTo(&ev1,LONG);
            ev0 = mod ? ev0 % mod : ev0;
            ev1 = mod ? ev1 % mod : ev0;
            if(((child[0].getEdgeHandle() == child[1].getEdgeHandle())
            && (ev0 == ev1)
            && setting.hasReductionRule(RULE_X))) {
            child[0].setValue(ev0 % mod);
            reduced = child[0];
            isMatch = 1;
            }
        }
        
        if (!isMatch) return normalizeNode(nodeLevel, child);
    /* =================================================================================================
    * BMXD for "Relation" (Terminal encoding)
    * ================================================================================================*/
    } else if (setting.isRelation() && em == TERMINAL) {
        bool isMatch = 0;
        bool isConstOne1, isConstOne2;
        bool isConstZero1, isConstZero2;
        isConstOne1 = child[1].isConstantOne();
        isConstOne2 = child[2].isConstantOne();
        isConstZero1 = child[1].isConstantZero();
        isConstZero2 = child[2].isConstantZero();
        /* ---------------------------------------------------------------------------------------------
        * Redundant X
        * --------------------------------------------------------------------------------------------*/
        if ((child[0].getEdgeHandle() == child[1].getEdgeHandle())
            && (child[1].getEdgeHandle() == child[2].getEdgeHandle())
            && (child[2].getEdgeHandle() == child[3].getEdgeHandle())
            && (child[0].getRule() == RULE_X)
            && setting.hasReductionRule(RULE_X)) {
            reduced = child[0];
            isMatch = 1;
        /* ---------------------------------------------------------------------------------------------
        * Identity I
        * --------------------------------------------------------------------------------------------*/
        } else if ((child[0].getEdgeHandle() == child[3].getEdgeHandle()) && (isRuleI(child[0].getRule()) || (nodeLevel - child[0].getNodeLevel() == 1))
                    && (isConstOne1 || isConstZero1) && (isConstOne2 || isConstZero2) && (isConstOne1 == isConstOne2)
                    && ((nodeLevel - child[0].getNodeLevel() == 1) || (hasRuleTerminalOne(child[0].getRule()) == isConstOne1))
                    && setting.hasReductionRule((isConstOne1)?RULE_I1:RULE_I0)) {
                reduced = child[0];
                reduced.setRule((isConstOne1)?RULE_I1:RULE_I0);
                isMatch = 1;            
        }
        // here means the forbidden node pattern found but its equivalent edge rules are not allowed
        if (!isMatch) return normalizeNode(nodeLevel, child);
    /* =================================================================================================
    * BMXD for "Relation" (Edge value encoding)
    * ================================================================================================*/
    } else if (setting.isRelation() && em == EDGE_PLUS) {
        // TBD
    }

    return reduced;
}

Edge Forest::mergeEdge(const Level beginLevel, const Level mergeLevel, const EdgeLabel label, const Edge& reduced, const Value& value)
{
#ifdef BRAVE_DD_FOREST_TRACE
    std::cout << "merge edge; beginLvl: "<< beginLevel << "; mergeLvl: " << mergeLevel << std::endl;
    std::cout << "<" << rule2String(unpackRule(label)) << ", " << unpackComp(label) << ", " << unpackSwap(label) << ", " << unpackSwapTo(label) << "> with ";
    reduced.print(std::cout);
    std::cout << std::endl;
#endif
    MergeType mt = setting.getMergeType();
    Edge merged;
    ReductionRule incomingRule = unpackRule(label);
    ReductionRule reducedRule = reduced.getRule();
    Level incomingSkip = beginLevel - mergeLevel;
    Level reducedSkip = mergeLevel - reduced.getNodeLevel();
    /* ---------------------------------------------------------------------------------------------
    * "Must" Compatible merge
    *
    *       1. Incoming edge rule is long X, edge "reduced" rule is long X.
    *       2. Incoming edge rule is long EL, edge "reduced" rule is long EL.
    *       3. Incoming edge rule is long EH, edge "reduced" rule is long EH.
    *       4. Incoming edge rule is long I, edge "reduced" rule is long I.
    *       5. Incoming edge rule is short N, edge "reduced" rule is any rule.
    *       
    *       The "merged" edge is set to be the "reduced" edge.
    * --------------------------------------------------------------------------------------------*/
    if (((incomingRule == reducedRule) && (incomingSkip > 0) && (reducedSkip > 0)
            && (isRuleEL(reducedRule) || isRuleEH(reducedRule) || isRuleI(reducedRule) || (reducedRule == RULE_X)))
        || (incomingSkip == 0)) {
        merged.setEdgeHandle(reduced.getEdgeHandle());
        if (setting.getEncodeMechanism() == EDGE_PLUS) {
            merged.setValue(reduced.getValue() + value);
        } else if (setting.getEncodeMechanism() == EDGE_PLUSMOD) {
            int mod = static_cast<int>(setting.getMaxRange());
            merged.setValue((reduced.getValue() + value) % mod);
        }
        return normalizeEdge(beginLevel, merged);
    }
    /* ---------------------------------------------------------------------------------------------
    * "Maybe" Compatible merge when [Push-down/ShortenX/ShortenI]
    *
    *       1. Edge "reduced" rule is short N.
    * 
    *      The edge "merged" rule MAY be set to be the incoming edge rule, while the swap bit, complement bit,
    *      target are set to be edge "reduced"'s. Or the edge "reduced" should be pushed down.
    * --------------------------------------------------------------------------------------------*/
    if (reducedSkip == 0) {
        if ((mt == PUSH_UP)
            || ((incomingRule == RULE_X) && (incomingSkip == 0))
            || ((incomingRule == RULE_X) && (incomingSkip > 0) && (mt == SHORTEN_X))
            || ((isRuleI(incomingRule)) && (incomingSkip > 0) && (mt == SHORTEN_I))) {
            merged = reduced;
            merged.setRule(incomingRule);
        } else {
            // check if the reduced edge can be pushed down, below TBD
            merged =reduced;
            merged.setRule(incomingRule);
        }
        return normalizeEdge(beginLevel, merged);
    }
    /* ---------------------------------------------------------------------------------------------
    * "Must" Incompatible merge
    *
    *       1. Incoming edge rule is long X, edge "reduced" rule is not long X.
    *       2. Incoming edge rule is EL, edge "reduced" rule is not EL.
    *       3. Incoming edge rule is EH, edge "reduced" rule is not EH.
    *       4. Incoming edge rule is AL or AH.
    *       5. Incoming edge rule is long I, edge "reduced" rule is long X.
    *
    * --------------------------------------------------------------------------------------------*/
    if ((incomingRule == RULE_X) && (incomingSkip > 0) && (reducedRule != RULE_X)) {
        // it could be MXD
        bool isRelation = setting.isRelation();
        /* Push-Up */
        if ((mt == PUSH_UP) || (mt == SHORTEN_X)) {
            // push-up one
            std::vector<Edge> childEdges;
            if (isRelation) {
                childEdges = std::vector<Edge>(4);
            } else {
                childEdges = std::vector<Edge>(2);
            }
            for (size_t i=0; i<childEdges.size(); i++) {
                childEdges[i] = reduced;
            }
            merged = normalizeNode(mergeLevel+1, childEdges);
        /* Push-Down */
        } else if ((mt == PUSH_DOWN) || (mt == SHORTEN_I)) {
            // For MXDs, here must be a incoming long X that merge with long I
            if (isRelation) {
                std::vector<Edge> childEdges(4);
                childEdges[0] = reduced;
                childEdges[3] = reduced;
                if (reducedSkip == 1) {
                    childEdges[0].setRule(RULE_X);
                    childEdges[3].setRule(RULE_X);
                }
                childEdges[1].handle = makeTerminal(INT, (int)hasRuleTerminalOne(reducedRule));
                childEdges[2].handle = makeTerminal(INT, (int)hasRuleTerminalOne(reducedRule));
                if (setting.getValType() == FLOAT || setting.getValType() == DOUBLE) {
                    childEdges[1].handle = makeTerminal(FLOAT, (float)hasRuleTerminalOne(reducedRule));
                    childEdges[2].handle = makeTerminal(FLOAT, (float)hasRuleTerminalOne(reducedRule));
                }
                for (size_t i=0; i<childEdges.size(); i++) {
                    childEdges[i] = normalizeEdge(mergeLevel, childEdges[i]);
                }
                merged = normalizeNode(mergeLevel+1, childEdges);
                merged.setRule(incomingRule);
            } else {
                // unreduce BDDs node for push-down, TBD
            }
        /* No merge */
        } else {
            // TBD
        }
    } else if ((isRuleEH(incomingRule)
                && (!isRuleEH(reducedRule) 
                    || (hasRuleTerminalOne(incomingRule) != hasRuleTerminalOne(reducedRule))))
                ||
                (isRuleEL(incomingRule)
                && (!isRuleEL(reducedRule) 
                    || (hasRuleTerminalOne(incomingRule) != hasRuleTerminalOne(reducedRule))))) {
        if (mt == PUSH_UP) {
            // merge a constant edge to terminal
            if (reduced.isConstantZero() || reduced.isConstantOne()) {
                if (hasRuleTerminalOne(incomingRule) == reduced.isConstantOne()) {
                    return reduced;
                }
            }
            // push-up one
            bool child = isRuleEH(incomingRule) ? 0 : 1;
            std::vector<Edge> childEdges(2);
            childEdges[child] = reduced;
            childEdges[!child].handle = makeTerminal(INT, (int)hasRuleTerminalOne(incomingRule));
            if (setting.getValType() == FLOAT || setting.getValType() == DOUBLE) {
                childEdges[!child].handle = makeTerminal(FLOAT, (float)hasRuleTerminalOne(incomingRule));
            }
            childEdges[!child].setRule(RULE_X);
            childEdges[!child] = normalizeEdge(mergeLevel, childEdges[!child]);
            merged = normalizeNode(mergeLevel+1, childEdges);
            merged.setRule((incomingSkip==1)?RULE_X:incomingRule);
        } else if (mt == PUSH_DOWN) {
            // TBD
        } else {
            // throw error!
        }
    } else if (isRuleAL(incomingRule) || isRuleAH(incomingRule)) {
        if (mt == PUSH_UP) {
            // merge a constant edge to terminal
            if (reduced.isConstantZero() || reduced.isConstantOne()) {
                if (hasRuleTerminalOne(incomingRule) == reduced.isConstantOne()) {
                    return reduced;
                }
            }
            // push-up all
            std::vector<Edge> childEdges(2);
            bool child = (isRuleAL(incomingRule)) ? 0 : 1;
            childEdges[child].handle = makeTerminal(INT, (int)hasRuleTerminalOne(incomingRule));
            if (setting.getValType() == FLOAT || setting.getValType() == DOUBLE) {
                childEdges[child].handle = makeTerminal(FLOAT, (float)hasRuleTerminalOne(incomingRule));
            }
            childEdges[child].setRule(RULE_X);
            EdgeLabel locLabel = 0;
            packRule(locLabel, RULE_X);
            for (Level k=mergeLevel+1; k<=beginLevel; k++) {
                childEdges[!child] = mergeEdge(k-1, mergeLevel, locLabel, reduced);
                childEdges[!child] = normalizeEdge(k-1, childEdges[!child]);
                childEdges[child] = normalizeEdge(k-1, childEdges[child]);
                merged = normalizeNode(k, childEdges);
                childEdges[child] = merged;
            }
        } else if (mt == PUSH_DOWN) {
            // TBD
        } else {
            // throw error!
        }
    } else if (isRuleI(incomingRule) && (reducedRule == RULE_X)) {
        if ((mt == PUSH_UP) || (mt == SHORTEN_I)) {
            // push-up one
            std::vector<Edge> childEdges(4);
            childEdges[0] = reduced;
            childEdges[3] = reduced;
            childEdges[1].handle = makeTerminal(INT, (int)hasRuleTerminalOne(incomingRule));
            childEdges[2].handle = makeTerminal(INT, (int)hasRuleTerminalOne(incomingRule));
            if (setting.getValType() == FLOAT || setting.getValType() == DOUBLE) {
                childEdges[1].handle = makeTerminal(FLOAT, (float)hasRuleTerminalOne(incomingRule));
                childEdges[2].handle = makeTerminal(FLOAT, (float)hasRuleTerminalOne(incomingRule));
            }
            for (size_t i=0; i<childEdges.size(); i++) {
                childEdges[i] = normalizeEdge(mergeLevel, childEdges[i]);
            }
            merged = normalizeNode(mergeLevel+1, childEdges);
            merged.setRule((incomingSkip == 1) ? RULE_X : incomingRule);
        } else if ((mt == PUSH_DOWN) || (mt == SHORTEN_X)) {
            // push-down one
            std::vector<Edge> childEdges(4);
            for (size_t i=0; i<childEdges.size(); i++) {
                childEdges[i] = reduced;
            }
            merged = normalizeNode(mergeLevel, childEdges);
            merged.setRule(incomingRule);
        }
    }
    return merged;
}

Edge Forest::mergeEdge(const Level beginLevel, const Level mergeLevel, const EdgeLabel label, const Edge& reduced, const Edge& target)
{
    Edge merged;
    ReductionRule incomingRule = unpackRule(label);
    ReductionRule reducedRule = reduced.getRule();
    Level incomingSkip = beginLevel - mergeLevel;
    Level reducedSkip  = mergeLevel - reduced.getNodeLevel();

    if (!setting.hasReductionRule(RULE_00)) {
        std::cout << "new merge edge!" << std::endl;
        exit(0);
    }
    if (incomingSkip == 0) {
        merged.setEdgeHandle(reduced.getEdgeHandle());
        return normalizeEdge(beginLevel, merged);
    }
    if (reducedSkip == 0) {
        merged = reduced;
        merged.setRule(incomingRule);
        return normalizeEdge(beginLevel, merged);
    }
    if (incomingRule != RULE_X && incomingRule != RULE_00 && incomingRule != RULE_11) {
        std::cout << "not supported incoming rule" << std::endl;
        exit(0);
    }
    if (reducedRule == RULE_X) {
        return reduced;
    } 

    Edge normalized;
    std::vector<Edge> child(2);
    EdgeLabel mergeLabel = 0;
    packRule(mergeLabel, incomingRule);
    if (incomingRule == RULE_X) {
        child[0] = reduced;
        child[1] = reduced;
        std::cout << beginLevel << "; " << mergeLevel << std::endl;
        if (beginLevel < mergeLevel + 1 ) {
            std::cout << "this is it" << std::endl;
        }
        normalized = normalizeNode(mergeLevel+1, child);
        normalized.setRule(RULE_X);
        return normalized;
    }

    if (incomingRule == RULE_00) {
        if (reducedRule == RULE_00) {
            return normalizeEdge(beginLevel, reduced);
        }
    
        if (reducedRule == RULE_11) {
            child[0] = target;
            child[1] = reduced;
            normalized = normalizeNode(mergeLevel+1, child);
            normalized.setRule((incomingSkip==1) ? RULE_X : incomingRule);
            return normalized;
        }
    }

    if (incomingRule == RULE_11) {
        if (reducedRule == RULE_11)
        {
            return normalizeEdge(beginLevel, reduced);
        }

        if (reducedRule == RULE_00)
        {
            child[1] = target;
            child[0] = reduced;
            normalized = normalizeNode(mergeLevel+1, child);
            normalized.setRule((incomingSkip==1) ? RULE_X : incomingRule);
            return normalized;
        }
    }
    std::cout << "This should not hit at merge edge. Case must not be covered";
    std::cout << "beginLevel: " << beginLevel << "; mergeLevel: " << mergeLevel << "; incoming: " << incomingRule << "; reducedRule : " << reducedRule << std::endl;
    exit(0);
}
Edge Forest::reduceEdge(const Level beginLevel, const EdgeLabel label, const Level nodeLevel, const std::vector<Edge>& down, const Value& value)
{
    /* check level */
    if (beginLevel < nodeLevel) {
        
        std::cout << "[BRAVE_DD] ERROR!\t reduceEdge(): Invalid level for incoming edge or target node!" << std::endl;
        std::cout << "down 0: ";
        down[0].print(std::cout);
        std::cout << "; down 1: ";
        down[1].print(std::cout);
        std::cout << std::endl;
        std::cout << beginLevel << "; " << nodeLevel << std::endl;
        exit(0);
    }
    /* check number of child */
    if ((setting.isRelation() && down.size() != 4) || (!setting.isRelation() && down.size() != 2)) {
        std::cout << "[BRAVE_DD] ERROR!\t reduceEdge(): Incorrect number of child edges!" << std::endl;
        exit(0);
    }

    /* copy the children info */
    std::vector<Edge> child = down;
#ifdef BRAVE_DD_FOREST_TRACE
    std::cout << "reduce edge; beginlvl: "<< beginLevel << "; nodelvl: " << nodeLevel << std::endl;
    for (size_t i=0; i<child.size(); i++) {
        child[i].print(std::cout);
        std::cout << std::endl;
    }
#endif
    /* push the flags or value down */
    CompSet ct = setting.getCompType();
    if (ct == COMP && unpackComp(label)) {                          // complement
        for (size_t i=0; i<child.size(); i++) child[i].complement();
    }
    SwapSet st = setting.getSwapType();
    if (!setting.isRelation() && unpackSwap(label)) {           // set: swap-one or swap-all
        if (st == ONE) {                                            // swap-one
            SWAP(child[0], child[1]);
        } else if (st == ALL) {                                     // swap-all
            SWAP(child[0], child[1]);
            child[0].swap();
            child[1].swap();
        }
    } else if (setting.isRelation()) {                          // relation: swap-from, swap-to, swap-from_to
        if ((st == FROM || st == FROM_TO) && unpackSwap(label)) {   // swap "from"
            SWAP(child[0], child[2]);
            SWAP(child[1], child[3]);
        }
        if ((st == TO || st == FROM_TO) && unpackSwapTo(label)) {   // swap "to"
            // to
            SWAP(child[0], child[1]);
            SWAP(child[2], child[3]);
        }
    }
    /* reduce node */
    Edge reduced;
    reduced = reduceNode(nodeLevel, child);    // this will take care of value on edge
#ifdef BRAVE_DD_FOREST_TRACE
    std::cout << "after reduce node:" << std::endl;
    reduced.print(std::cout);
    std::cout << std::endl;
#endif
    /* incoming edge rule for merge */
    EdgeLabel mergeLabel = 0;
    packRule(mergeLabel, unpackRule(label));
    /* merge incoming edge with reduced node */
    if (setting.getEncodeMechanism() == TERMINAL) {
        if (unpackRule(label) == RULE_00) {
            reduced = mergeEdge(beginLevel, nodeLevel, mergeLabel, reduced, child[0]);
        } else if (unpackRule(label) == RULE_11) {
            reduced = mergeEdge(beginLevel, nodeLevel, mergeLabel, reduced, child[1]);
        } else {
            reduced = mergeEdge(beginLevel, nodeLevel, mergeLabel, reduced);
        }
    } else {
        reduced = mergeEdge(beginLevel, nodeLevel, mergeLabel, reduced, value);
    }
#ifdef BRAVE_DD_FOREST_TRACE
    std::cout << "after merge edge:" << std::endl;
    reduced.print(std::cout);
    std::cout << std::endl;
#endif
    return reduced;
}

void Forest::markSweep()
{
    // sweep unique table
    uniqueTable->sweep();
    // sweep computing table (cache) related to this forest
    UOPs.sweepCache(this);
    BOPs.sweepCache(this);
    SOPs.sweepCache(this);

    // sweep
    nodeMan->sweep();
    // unmark
    unmark();
}

void Forest::reportNodesNum(std::ostream& out) const
{
    uint64_t total = 0;
    for (Level k=1; k<=setting.getNumVars(); k++) {
        out << "Level " << k << ": " << getNodeManUsed(k) << "\n";
        total += getNodeManUsed(k);
    }
    out << "Total nodes: " << total << "\n";
    out << "Peak nodes: " << nodeMan->numRealPeak() << "\n";
}

/// Helper Methods ==============================================
bool Forest::checkCompatibility() const
{
    bool ans = 1;
    // TBD
    if (!ans) {
        std::cout << "[BRAVE_DD] Error!\t The ForestSetting consistency check failed!"<< std::endl;
        setting.output(std::cerr, 0);
        exit(1);
    }
    return ans;
}

char Forest::isSwapAllUseless(Edge& e) {
    if (e.getNodeLevel() == 0) return 1;
    // TBD
    return 0;
}

Edge Forest::unreduceEdge(const Level level, const Edge& edge)
{
    Edge ans;
    // TBD
    ans = edge;
    return ans;
}

Edge Forest::buildHalf(const Level beginLvl, const Level endLvl, const Edge& e1, const Edge& e2, const bool isLow)
{
    Edge ans;
    EdgeLabel root = 0;
    /* Base case that can directly call reduce edge*/
    if (beginLvl == endLvl) {
        std::vector<Edge> child(2);
        child[0] = e1;
        child[1] = e2;
        packRule(root, RULE_X);
        return reduceEdge(beginLvl, root, endLvl, child);
    }
    /* Base cases that can directly return a long edge */
    if (e1 == e2) {
        if (e1.getRule() == RULE_X) return e1;
        // constant long edge, in case X is not allowed
        if (e1.getNodeLevel() == 0) {
            bool isOne = isTerminalOne(e1.getEdgeHandle());
            bool isZero = isTerminalZero(e1.getEdgeHandle());
            if ((hasRuleTerminalOne(e1.getRule()) == (e1.getComp() ^ isOne)) && (isOne || isZero)) {
                return e1;
            }
        } else {
            std::vector<Edge> child(2);
            child[0] = e1;
            child[1] = e2;
            packRule(root, RULE_X);
            return reduceEdge(beginLvl, root, endLvl, child);
        }
    }
    if (isLow) {
        // low pattern
        if (e1.isConstantZero() || e1.isConstantOne()) {
            ReductionRule incomingRule = e1.isConstantZero() ? RULE_EL0 : RULE_EL1;
            packRule(root, incomingRule);
            ans = mergeEdge(beginLvl, endLvl-1, root, e2);
            ans = normalizeEdge(beginLvl, ans);
            return ans;
        }
        if (e2.isConstantZero() || e2.isConstantOne()) {
            ReductionRule incomingRule = e2.isConstantZero() ? RULE_AH0 : RULE_AH1;
            packRule(root, incomingRule);
            ans = mergeEdge(beginLvl, endLvl-1, root, e1);
            ans = normalizeEdge(beginLvl, ans);
            return ans;
        }
    } else {
        // high pattern
        if (e2.isConstantZero() || e2.isConstantOne()) {
            ReductionRule incomingRule = e2.isConstantZero() ? RULE_EH0 : RULE_EH1;
            packRule(root, incomingRule);
            ans = mergeEdge(beginLvl, endLvl-1, root, e1);
            ans = normalizeEdge(beginLvl, ans);
            return ans;
        }
        if (e1.isConstantZero() || e1.isConstantOne()) {
            ReductionRule incomingRule = e1.isConstantZero() ? RULE_AL0 : RULE_AL1;
            packRule(root, incomingRule);
            ans = mergeEdge(beginLvl, endLvl-1, root, e2);
            ans = normalizeEdge(beginLvl, ans);
            return ans;
        }
    }
    /* Now we need to build this pattern */
    std::vector<Edge> child(2);
    packRule(root, RULE_X);
    ans = isLow?e2:e1; 
    for (Level i=endLvl; i<=beginLvl; i++) {
        child[0] = isLow ? mergeEdge(i-1, endLvl-1, root, e1) : ans;
        child[1] = isLow ? ans : mergeEdge(i-1, endLvl-1, root, e2);
        ans = reduceEdge(i, root, i, child);
    }
    return ans;
}

Edge Forest::buildUmb(const Level beginLvl, const Level endLvl, const Edge& e1, const Edge& e2, const Edge& e3)
{
    Edge ans;
    EdgeLabel root = 0;
    std::vector<Edge> child(2);
    packRule(root, RULE_X);
    child[0] = buildHalf(beginLvl-1, endLvl, e1, e2, 0);
    child[1] = buildHalf(beginLvl-1, endLvl, e2, e3, 1);
    ans = reduceEdge(beginLvl, root, beginLvl, child);
    return ans;
}

void Forest::markNodes(const Edge& edge) const
{
    char numChild = (setting.isRelation()) ? 4 : 2;
    if (edge.getNodeLevel() > 0) {
        if (!getNode(edge).isMarked()) {
#ifdef BRAVE_DD_FOREST_TRACE
    std::cout << "marking node " << edge.getNodeHandle() << " at level " << edge.getNodeLevel() << std::endl;
#endif
            getNode(edge).mark();
            for (char i=0; i<numChild; i++) {
                markNodes(getChildEdge(edge.getNodeLevel(), edge.getNodeHandle(), i));
            }
        }
    }
}

void Forest::markNodes(const EdgeHandle& edge) const
{
    char numChild = (setting.isRelation()) ? 4 : 2;
    Level level = unpackLevel(edge);
    if (level > 0) {
        NodeHandle target = unpackTarget(edge);
        if (!getNode(level, target).isMarked()) {
#ifdef BRAVE_DD_FOREST_TRACE
    std::cout << "marking node " << target << " at level " << level << std::endl;
#endif
            getNode(edge).mark();
            for (char i=0; i<numChild; i++) {
                markNodes(getChildEdgeHandle(level, target, i));
            }
        }
    }
}
