#include "../src/brave_dd.h"
#include <sstream>
#include <unordered_map>
#include <string>
#include "timer.h"

using namespace BRAVE_DD;

std::unordered_map<uint16_t, Edge> setCache;
Edge buildSetEdge(Forest *forest, uint16_t numvars, uint16_t targetLevel,
                  std::vector<uint16_t> markings) {
  EdgeLabel label = 0;
  packRule(label, RULE_X);

  if (setCache.find(targetLevel) != setCache.end()) {
    return setCache[targetLevel];
  }

  std::vector<Edge> child(2);
  uint16_t index = numvars - targetLevel;
  bool isTarget = false;

  if (targetLevel == 1) {
    if (markings[index]) {
      child[0].setEdgeHandle(makeTerminal(INT, 0));
      child[1].setEdgeHandle(makeTerminal(INT, 1));
    } else {
      child[0].setEdgeHandle(makeTerminal(INT, 1));
      child[1].setEdgeHandle(makeTerminal(INT, 0));
    }
    child[0].setRule(RULE_X);
    child[1].setRule(RULE_X);
    Edge result = forest->reduceEdge(targetLevel, label, targetLevel, child);
    setCache[targetLevel] = result;
    return result;
  }
  if (markings[index]) {
    child[0].setEdgeHandle(makeTerminal(INT, 0));
    child[0].setRule(RULE_X);
    child[1] = buildSetEdge(forest, numvars, targetLevel - 1, markings);
  } else {
    child[0] = buildSetEdge(forest, numvars, targetLevel - 1, markings);
    child[1].setEdgeHandle(makeTerminal(INT, 0));
    child[1].setRule(RULE_X);
  }
  Edge result = forest->reduceEdge(targetLevel, label, targetLevel, child);
  setCache[targetLevel] = result;
  return result;
}

Func buildInit(Forest *forest, std::vector<uint16_t> markings) {
  Func res(forest);
  uint16_t levels = forest->getSetting().getNumVars();

  Edge root = buildSetEdge(forest, levels, levels, markings);
  res.setEdge(root);
  setCache.clear();

  return res;
}

std::unordered_map<uint16_t, Edge> relCache;
Edge buildRelEdge(Forest *forest, uint16_t numvars, uint16_t targetLevel,
                  std::vector<uint16_t> inputs, std::vector<uint16_t> outputs) {
  EdgeLabel label = 0;
  packRule(label, RULE_I0);
  if (relCache.find(targetLevel) != relCache.end()) {
    return relCache[targetLevel];
  }

  std::vector<Edge> child(4);
  uint16_t index = numvars - targetLevel;

  bool isInput = false;
  if (std::find(inputs.begin(), inputs.end(), index) != inputs.end())
    isInput = true;
  bool isOutput = false;
  if (std::find(outputs.begin(), outputs.end(), index) != outputs.end())
    isOutput = true;

  if (targetLevel == 1) {
    if (isInput && isOutput) {
      child[0].setEdgeHandle(makeTerminal(INT, 0));
      child[1].setEdgeHandle(makeTerminal(INT, 0));
      child[2].setEdgeHandle(makeTerminal(INT, 0));
      child[3].setEdgeHandle(makeTerminal(INT, 1));
    } else if (isOutput) {
      child[0].setEdgeHandle(makeTerminal(INT, 0));
      child[1].setEdgeHandle(makeTerminal(INT, 1));
      child[2].setEdgeHandle(makeTerminal(INT, 0));
      child[3].setEdgeHandle(makeTerminal(INT, 0));
    } else if (isInput) {
      child[0].setEdgeHandle(makeTerminal(INT, 0));
      child[1].setEdgeHandle(makeTerminal(INT, 0));
      child[2].setEdgeHandle(makeTerminal(INT, 1));
      child[3].setEdgeHandle(makeTerminal(INT, 0));
    } else {
      child[0].setEdgeHandle(makeTerminal(INT, 1));
      child[1].setEdgeHandle(makeTerminal(INT, 0));
      child[2].setEdgeHandle(makeTerminal(INT, 0));
      child[3].setEdgeHandle(makeTerminal(INT, 1));
    }
    child[0].setRule(RULE_X);
    child[1].setRule(RULE_X);
    child[2].setRule(RULE_X);
    child[3].setRule(RULE_X);
    Edge result = forest->reduceEdge(targetLevel, label, targetLevel, child);
    relCache[targetLevel] = result;
    return result;
  }
  if (isInput && isOutput) {
    child[0].setEdgeHandle(makeTerminal(INT, 0));
    child[0].setRule(RULE_X);
    child[1].setEdgeHandle(makeTerminal(INT, 0));
    child[1].setRule(RULE_X);
    child[2].setEdgeHandle(makeTerminal(INT, 0));
    child[2].setRule(RULE_X);
    child[3] = buildRelEdge(forest, numvars, targetLevel - 1, inputs, outputs);

  } else if (isOutput) {
    child[0].setEdgeHandle(makeTerminal(INT, 0));
    child[0].setRule(RULE_X);
    child[1] = buildRelEdge(forest, numvars, targetLevel - 1, inputs, outputs);
    child[2].setEdgeHandle(makeTerminal(INT, 0));
    child[2].setRule(RULE_X);
    child[3].setEdgeHandle(makeTerminal(INT, 0));
    child[3].setRule(RULE_X);

  } else if (isInput) {
    child[0].setEdgeHandle(makeTerminal(INT, 0));
    child[0].setRule(RULE_X);
    child[1].setEdgeHandle(makeTerminal(INT, 0));
    child[1].setRule(RULE_X);
    child[2] = buildRelEdge(forest, numvars, targetLevel - 1, inputs, outputs);
    child[3].setEdgeHandle(makeTerminal(INT, 0));
    child[3].setRule(RULE_X);
  } else {
    child[0] = buildRelEdge(forest, numvars, targetLevel - 1, inputs, outputs);
    child[1].setEdgeHandle(makeTerminal(INT, 0));
    child[1].setRule(RULE_X);
    child[2].setEdgeHandle(makeTerminal(INT, 0));
    child[2].setRule(RULE_X);
    child[3] = buildRelEdge(forest, numvars, targetLevel - 1, inputs, outputs);
  }
  Edge result = forest->reduceEdge(targetLevel, label, targetLevel, child);
  relCache[targetLevel] = result;
  return result;
}

Func buildTransition(Forest *forest, std::vector<uint16_t> inputs,
                     std::vector<uint16_t> outputs) {
  Func res(forest);
  uint16_t levels = forest->getSetting().getNumVars();
  Edge root = buildRelEdge(forest, levels, levels, inputs, outputs);
  res.setEdge(root);
  return res;
}

void compute_saturation(Forest *forest1, const Func &target,
                        const std::vector<Func> &relations) {
  forest1->getSetting().output(std::cerr);
  Func states_Sat(forest1);
  // Timer start
  std::cerr << "Begin saturation" << std::endl;
  timer watch;
  watch.note_time();
  apply(SATURATE, target, relations, states_Sat);
  /* Timer end */
  watch.note_time();
  std::cerr << "Peak Nodes: " << forest1->getNodeManPeak() << ","
            << "Final Nodes: " << forest1->getNodeManUsed(states_Sat) << ","
            << "Operation time: " << watch.get_last_seconds() << std::endl;
  std::cout << forest1->getNodeManPeak() << " , "
            << forest1->getNodeManUsed(states_Sat) << ", "
            << watch.get_last_seconds();
}
int main(int argc, const char **argv) {
  // file bdd algorithm

  if (argc == 1) {
    std::cout << "command <filename> <bdd-type>" << std::endl;
    std::cout << "<bdd-type>" << std::endl;
    std::cout << "cesr -> CESRBDD" << std::endl;
    std::cout << "rex -> REXBDD" << std::endl;
    std::cout << "roar -> ROARBDD" << std::endl;
    exit(0);
  }

  if (argc != 3) {
    std::cout << "Arg doesn't match!" << std::endl;
    exit(0);
  }

  std::string filepath = std::string(argv[1]);

  
  std::ifstream file(filepath);
  if (!file) {
    std::cout << "No such file";
    exit(0);
  }

  std::string line;
  std::getline(file, line); // initial-marking

  uint16_t x;
  std::vector<uint16_t> initialMarking;
  std::getline(file, line);

  for (std::istringstream stream(line); stream >> x;)
    initialMarking.push_back(x);

  std::vector<std::vector<uint16_t>> inputs;
  std::vector<std::vector<uint16_t>> outputs;
  uint64_t count = 0;

  while (true) {
    std::getline(file, line); // transition
    if (line == "done")
      break;
    std::getline(file, line); // input

    std::vector<uint16_t> input;

    for (std::istringstream stream(line); stream >> x;)
      input.push_back(x);
    inputs.push_back(input);

    std::vector<uint16_t> output;

    std::getline(file, line); // output

    for (std::istringstream stream(line); stream >> x;)
      output.push_back(x);
    outputs.push_back(output);
  }

  uint16_t levels = initialMarking.size();
  std::cout << levels << ", ";
  PredefForest ddType;
  if (strcmp(argv[2], "fbdd") == 0) ddType = PredefForest::FBDD;
  if (strcmp(argv[2], "zbdd") == 0) ddType = PredefForest::ZBDD;
  if (strcmp(argv[2], "esrbdd") == 0) ddType = PredefForest::ESRBDD;
  if (strcmp(argv[2], "rex") == 0) ddType = PredefForest::REXBDD;
  if (strcmp(argv[2], "cesr") == 0) ddType = PredefForest::CESRBDD;
  if (strcmp(argv[2], "roar") == 0) ddType = PredefForest::ROAR;
  if (strcmp(argv[2], "or") == 0) ddType = PredefForest::OR;
  ForestSetting setting1(ddType, levels);
  ForestSetting setting2(PredefForest::FBMXD, levels);

  Forest *forest1 = new Forest(setting1);
  Forest *forest2 = new Forest(setting2);

  Func res1 = buildInit(forest1, initialMarking);

  std::vector<Func> relations;
  for (uint32_t i = 0; i < inputs.size(); i++) {
    relCache.clear();
    relations.push_back(buildTransition(forest2, inputs[i], outputs[i]));
    relCache.clear();
  }
  // setting1.output(std::cerr);
compute_saturation(forest1, res1, relations);

  delete forest1;
  delete forest2;
   // Ok we are comapring the function now
}
