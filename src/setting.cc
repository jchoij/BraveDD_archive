#include "setting.h"
#include "settings/reductions.h"
#include <regex>

using namespace BRAVE_DD;
// ******************************************************************
// *                                                                *
// *                                                                *
// *                      VarDomain methods                         *
// *                                                                *
// *                                                                *
// ******************************************************************

VarDomain::VarDomain(Level size)
{
    maxLevel = size;
    // ordering TBD
}
VarDomain::~VarDomain()
{
    //
}

// ******************************************************************
// *                                                                *
// *                                                                *
// *                        Setting methods                         *
// *                                                                *
// *                                                                *
// ******************************************************************

ForestSetting::ForestSetting(const unsigned numVals)
:domain(numVals), range(BOOLEAN, INT), flags(ONE, COMP)
{
    // User defined number of variables
    // default settings: RexBDD
    reductions = Reductions(REX);
    encodingType = TERMINAL;
    mergeType = PUSH_UP;
    name = "RexBDD";
}

ForestSetting::ForestSetting(const PredefForest type, const unsigned numVals, const long maxRange)
:domain(numVals), range(maxRange), flags(NO_SWAP, NO_COMP)
{
    // default setting
    encodingType = TERMINAL;
    mergeType = NO_MERGE;
    if (type == PredefForest::REXBDD) {
        // setting for RexBDD
        reductions = Reductions(REX);
        flags.setSwapType(ONE);
        flags.setCompType(COMP);
        mergeType = PUSH_UP;
        name = "RexBDD";
    } else if (type == PredefForest::QBDD) {
        // setting for QBDD
        reductions = Reductions(QUASI);
        name = "QBDD";
    } else if (type == PredefForest::FBDD) {
        // setting for FBDD
        reductions = Reductions(FULLY);
        name = "FBDD";
    } else if (type == PredefForest::CFBDD) {
        // setting for CFBDD
        reductions = Reductions(FULLY);
        flags.setCompType(COMP);
        name = "CFBDD";
    } else if (type == PredefForest::SFBDD) {
        // setting for SFBDD
        reductions = Reductions(FULLY);
        flags.setSwapType(ONE);
        name = "SFBDD";
    } else if (type == PredefForest::CSFBDD) {
        // setting for CSFBDD
        reductions = Reductions(FULLY);
        flags.setSwapType(ONE);
        flags.setCompType(COMP);
        name = "CSFBDD";
    } else if (type == PredefForest::ZBDD) {
        // setting for ZBDD
        reductions = Reductions(ZERO_SUP);
        name = "ZBDD";
        mergeType = PUSH_UP;
    } else if (type == PredefForest::ESRBDD) {
        // setting for ESRBDD
        reductions = Reductions(USER_DEFINED);
        addReductionRule(RULE_X);
        addReductionRule(RULE_EL0);
        addReductionRule(RULE_EH0);
        mergeType = PUSH_UP;
        name = "ESRBDD";
    } else if (type == PredefForest::CESRBDD) {
        // setting for CESRBDD
        reductions = Reductions(USER_DEFINED);
        addReductionRule(RULE_X);
        addReductionRule(RULE_EL0);
        addReductionRule(RULE_EL1);
        addReductionRule(RULE_EH0);
        addReductionRule(RULE_EH1);
        flags.setCompType(COMP);
        mergeType = PUSH_UP;
        name = "CESRBDD";
    } else if (type == PredefForest::QBMXD) {
        // setting for QBMxD
        reductions = Reductions(QUASI_QUASI);
        name = "QBMxD";
    } else if (type == PredefForest::FBMXD) {
        // setting for FBMxD
        reductions = Reductions(FULLY_FULLY);
        mergeType = PUSH_UP;
        name = "FBMxD";
    } else if (type == PredefForest::IBMXD) {
        // setting for IBMxD
        reductions = Reductions(IDENTITY_IDENTITY);
        mergeType = PUSH_UP;
        name = "IBMxD";
    } else if (type == PredefForest::ESRBMXD) {
        // setting for ESRBMxD
        reductions = Reductions(FULLY_IDENTITY);
        mergeType = PUSH_UP;
        name = "ESRBMxD";
    } else if (type == PredefForest::MTBDD) {
        // setting for MTBDD
        reductions = Reductions(FULLY);
        name = "MTBDD";
        encodingType = TERMINAL;
        range = Range(RangeType::NNINTEGER,INT);
    } else if (type == PredefForest::EVQBDD) {
        // setting for EV+QBDD
        reductions = Reductions(QUASI);
        name = "EVQBDD";
        encodingType = EDGE_PLUS;
        range = Range(RangeType::NNINTEGER,INT);
    } else if (type == PredefForest::EVFBDD) {
        // setting for EVFBDD
        reductions = Reductions(FULLY);
        name = "EVFBDD";
        encodingType = EDGE_PLUS;
        range = Range(RangeType::NNINTEGER,INT);
    } else if (type == PredefForest::EVMODQBDD) {
         // setting for EV%QBDD
         reductions = Reductions(QUASI);
         name = "EVMODQBDD";
         encodingType = EDGE_PLUSMOD;
         range = Range(RangeType::NNINTEGER,INT);
         // Effectively this will act as if there is no mu
         // User will have to set mod value in order to benefit from it
         range.setMaxRange(std::numeric_limits<unsigned long>::max());
    } else if (type == PredefForest::EVMODFBDD) {
        // setting for EV%FBDD
        reductions = Reductions(FULLY);
        name = "EVMODFBDD";
        encodingType = EDGE_PLUSMOD;
        range = Range(RangeType::NNINTEGER,INT);
        // Effectively this will act as if there is no mu
        // User will have to set mod value in order to benefit from it
        range.setMaxRange(std::numeric_limits<unsigned long>::max());
    } else if (type == PredefForest::EVQBMXD) {
        // setting for EVQBMxD
    } else if (type == PredefForest::EVFBMXDs) {
        // setting for EVFBMxD
    } else if (type == PredefForest::ROAR) {
        reductions = Reductions(ROAR);
        mergeType = PUSH_UP;
        name = "ROAR";
        setCompType(COMP);
        setSwapType(ONE);
    } else if (type == PredefForest::OR) {
        reductions = Reductions(OR);
        mergeType = PUSH_UP;
        name = "OR";
    } else {
        // Unknown predefined BDD or BMxD
        std::cout << "[BRAVE_DD] ERROR!\t Unknown BDD/MxD!" << std::endl;
        exit(0);
    }
}

ForestSetting::ForestSetting(const std::string& bdd, const unsigned numVals, const long maxRange)
:domain(numVals), range(maxRange), flags(NO_SWAP, NO_COMP)
{
    // default setting
    encodingType = TERMINAL;
    mergeType = NO_MERGE;
    // convert to all lower case
    std::string bddLower;
    bddLower.resize(bdd.size());
    std::transform(bdd.begin(), bdd.end(), bddLower.begin(), ::tolower);
    // BDDs
    if (bddLower == "rexbdd") {
        // setting for RexBDD
        reductions = Reductions(REX);
        flags.setSwapType(ONE);
        flags.setCompType(COMP);
        mergeType = PUSH_UP;
        name = "RexBDD";
    } else if (bddLower == "qbdd") {
        // setting for QBDD
        reductions = Reductions(QUASI);
        name = "QBDD";
    } else if (bddLower == "cqbdd") {
        // setting for CQBDD
        reductions = Reductions(QUASI);
        flags.setCompType(COMP);
        name = "CQBDD";
    } else if (bddLower == "sqbdd") {
        // setting for SQBDD
        reductions = Reductions(QUASI);
        flags.setSwapType(ONE);
        name = "SQBDD";
    } else if (bddLower == "csqbdd") {
        // setting for CSQBDD
        reductions = Reductions(QUASI);
        flags.setSwapType(ONE);
        flags.setCompType(COMP);
        name = "CSQBDD";
    } else if (bddLower == "fbdd") {
        // setting for FBDD
        reductions = Reductions(FULLY);
        name = "FBDD";
    } else if (bddLower == "cfbdd") {
        // setting for CFBDD
        reductions = Reductions(FULLY);
        flags.setCompType(COMP);
        name = "CFBDD";
    } else if (bddLower == "sfbdd") {
        // setting for SFBDD
        reductions = Reductions(FULLY);
        flags.setSwapType(ONE);
        name = "SFBDD";
    } else if (bddLower == "csfbdd") {
        // setting for CSFBDD
        reductions = Reductions(FULLY);
        flags.setSwapType(ONE);
        flags.setCompType(COMP);
        name = "CSFBDD";
    } else if (bddLower == "zbdd") {
        // setting for ZBDD
        reductions = Reductions(ZERO_SUP);
        name = "ZBDD";
        mergeType = PUSH_UP;
    } else if (bddLower == "esrbdd") {
        // setting for ESRBDD
        reductions = Reductions(USER_DEFINED);
        addReductionRule(RULE_X);
        addReductionRule(RULE_EL0);
        addReductionRule(RULE_EH0);
        mergeType = PUSH_UP;
        name = "ESRBDD";
    } else if (bddLower == "cesrbdd") {
        // setting for CESRBDD
        reductions = Reductions(USER_DEFINED);
        addReductionRule(RULE_X);
        addReductionRule(RULE_EL0);
        addReductionRule(RULE_EH0);
        addReductionRule(RULE_EL1);
        addReductionRule(RULE_EH1);
        flags.setCompType(COMP);
        mergeType = PUSH_UP;
        name = "CESRBDD";
    } else if (bddLower == "evqbdd" || bddLower == "ev+qbdd") {
        // setting for EV+QBDD
        reductions = Reductions(QUASI);
        name = "EVQBDD";
        encodingType = EDGE_PLUS;
        range = Range(RangeType::NNINTEGER,INT);
    } else if (bddLower == "ev%qbdd" || bddLower == "evmodqbdd") {
        // setting for EV%QBDD
        reductions = Reductions(QUASI);
        name = "EVMODQBDD";
        encodingType = EDGE_PLUSMOD;
        range = Range(RangeType::NNINTEGER,INT);
        // Effectively this will act as if there is no mu
        // User will have to set mod value in order to benefit from it
        range.setMaxRange(std::numeric_limits<unsigned long>::max());
    } else if (bddLower == "mtbdd") {
        // setting for MTBDD
        reductions = Reductions(FULLY);
        name = "MTBDD";
        encodingType = TERMINAL;
        range = Range(RangeType::NNINTEGER,INT);
    } else if (bddLower == "ev*qbdd") {
        // setting for EV*QBDD
    } else if (bddLower == "evfbdd" || bddLower == "ev+fbdd") {
        // setting for EV+FBDD
        reductions = Reductions(FULLY);
        name = "EVFBDD";
        encodingType = EDGE_PLUS;
        range = Range(RangeType::NNINTEGER,INT);
    } else if (bddLower == "sevfbdd" || bddLower == "sev+fbdd") {
        // setting for EV+FBDD
        reductions = Reductions(FULLY);
        flags.setSwapType(ONE);
        name = "SEVFBDD";
        encodingType = EDGE_PLUS;
        range = Range(RangeType::NNINTEGER,INT);
    } else if (bddLower == "ev%fbdd" || bddLower == "evmodfbdd") {
        // setting for EV%FBDD
        reductions = Reductions(FULLY);
        name = "EVMODFBDD";
        encodingType = EDGE_PLUSMOD;
        range = Range(RangeType::NNINTEGER,INT);
        // Effectively this will act as if there is no mu
        // User will have to set mod value in order to benefit from it
        range.setMaxRange(std::numeric_limits<unsigned long>::max());
    }
    // MxDs
    else if (bddLower == "qbmxd") {
        // setting for QBMxD
        reductions = Reductions(QUASI_QUASI);
        name = "QBMxD";
    } else if (bddLower == "fbmxd") {
        // setting for FBMxD
        reductions = Reductions(FULLY_FULLY);
        mergeType = PUSH_UP;
        name = "FBMxD";
    } else if (bddLower == "ibmxd") {
        // setting for IBMxD
        reductions = Reductions(IDENTITY_IDENTITY);
        mergeType = PUSH_UP;
        name = "IBMxD";
    } else if (bddLower == "esrbmxd") {
        // setting for ESRBMxD
        reductions = Reductions(FULLY_IDENTITY);
        mergeType = PUSH_UP;
        name = "ESRBMxD";
    }
    else if (bddLower == "mtbmxd") {
        // setting for MTBMxD
    } else if (bddLower == "evbqmxd" || bddLower == "ev+bqmxd") {
        // setting for EV+QBMxD
    } else if (bddLower == "evfbmxd" || bddLower == "ev+fbmxd") {
        // setting for EV+FBMxD
    } else {
        // Unknown predefined BDD or BMxD
        std::cout << "[BRAVE_DD] ERROR!\t Unknown BDD/MxD: " << bdd << std::endl;
        exit(0);
    }
}

ForestSetting::~ForestSetting()
{
    //
}

void ForestSetting::output(std::ostream& out, int format) const
{
    if (format == 0) {
        // name 
        out<<"============================== Settings ============================="<<std::endl;
        out<<"\tName:\t\t\t"<<name<<std::endl;
        // number of variables
        out<<"\tNumber of variables:\t"<<getNumVars()<<std::endl;
        // relation or set
        std::string isRel = isRelation()?"Relation":"Set";
        if (isRelation()) {
            isRel += ", dimension = ";
            isRel += std::to_string(reductions.getDim());
        }
        out<<"\tEncoding purpose:\t"<<isRel<<std::endl;
        // range type
        RangeType rt = getRangeType();
        std::string rangeType = rangeType2String(rt);
        if (rt == FINITE || rt == BOOLEAN) {
            rangeType += ": N = ";
            rangeType += std::to_string(getMaxRange());
        }
        out<<"\tRange type:\t\t"<<rangeType<<std::endl;
        // range value type
        out<<"\tRange value type:\t"<<valueType2String(getValType())<<std::endl;
        // special values
        std::string specialVal;
        if (!hasNegInf()&&!hasPosInf()&&!hasUnDef()) {
            specialVal = ":\tNO Special";
        } else {
            specialVal = ":\t";
            if (hasNegInf()) specialVal += "NegInf  ";
            if (hasPosInf()) specialVal += "PosInf  ";
            if (hasUnDef()) specialVal += "UnDef  ";
        }
        out<<"\tRange special values"<<specialVal<<std::endl;
        // reduction type
        out<<"\tReduction type:\t\t"<<reductionType2String(getReductionType())<<std::endl;
        // reduction rules
        out<<"\tNumber of rules:\t"<<getReductionSize()<<std::endl;
        std::string rules = "";
        for (int rule=0; rule<=12; rule++) {
            if (hasReductionRule((ReductionRule)rule)) {
                rules += rule2String((ReductionRule)rule);
                rules += "  ";
            }
        }
        out<<"\tReduction rules:\t"<<rules<<std::endl;
        // flags
        out<<"\tSwap type:\t\t"<<swapSet2String(getSwapType())<<std::endl;
        out<<"\tComplement allowed:\t"<<compSet2String(getCompType())<<std::endl;
        // encoding type
        out<<"\tEncoding Mechanism:\t"<<encodeMechanism2String(getEncodeMechanism());
        if (getEncodeMechanism()==EDGE_PLUSMOD) out<<": mod = "<<getMaxRange();
        out<<std::endl;
        // merge type
        out<<"\tMerge type:\t\t"<<mergeType2String(getMergeType(), isRelation())<<std::endl;
        out<<"============================ Settings End ==========================="<<std::endl;
    } else if (format == 1) {
        //
    } else {
        //
    }
}
