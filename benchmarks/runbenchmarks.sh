#!/usr/bin/env bash
TIMEOUT=300
TIMEOUT_CMD="timeout $TIMEOUT"

tests=(diverge/Diverge list-assoc/ListAssoc list-ident/ListIdent add-commute/AddCommute optimize/Optimize)

echo "Benchmark run starting at $(date)"
echo "Commit: $(git rev-parse --verify HEAD)"
echo "Timeout: $TIMEOUT seconds"

function runTest {
  printf "$1 $2... "
  RESULT=$($TIMEOUT_CMD $1 $2 2>/dev/null)
  STATUS=$?
  if [[ $STATUS -eq 124  ]]; then
      echo "Timeout"
  elif [[ $STATUS -eq 0 ]]; then
      echo "OK"
  else 
      echo "Failed $STATUS"
  fi
}

function runSMTTest {
  printf "cvc4 $1... "
  RESULT=$($TIMEOUT_CMD cvc4 $1 2>/dev/null)
  if [[ $? -eq 124  ]]; then
      echo "Timeout"
  elif [[ $RESULT == 'unsat' ]]; then
      echo "OK"
  else 
      echo "Failed"
  fi
}

function runZenoTest {
  printf "zeno -I $1... "
  RESULT=$($TIMEOUT_CMD zeno -I $1 2>/dev/null)
  if [[ $? -eq 124  ]]; then
      echo "Timeout"
  elif [[ $RESULT == *"Could neither prove nor disprove"* ]]; then
      echo "Failed"
  else 
      echo "OK"
  fi
}

echo "Running LH tests"
for test in ${tests[@]}; do
  runTest "liquid" "$test.hs"
done

echo "Running Coq tests"
for test in ${tests[@]}; do
  runTest "coqc" "${test}.v"
done

echo "Running Agda tests"
for test in ${tests[@]}; do
  runTest "agda" "${test}.agda"
done

echo "Running Lean tests"
for test in ${tests[@]}; do
  runTest "lean" "${test}.lean"
done

echo "Running Isabelle tests"
for test in ${tests[@]}; do
  runTest "isabelle process -o quick_and_dirty -T" "$test"
done

echo "Running Zeno tests"
for test in ${tests[@]}; do
  runZenoTest "${test}Zeno.hs"
done

echo "Running SMT tests"
for test in ${tests[@]}; do
  runSMTTest $test.smt2
done



