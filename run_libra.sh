#/usr/bin/env bash

# set -e

# sbt assembly
JAR_NAME=./target/scala-2.13/libra-assembly-0.1.0-SNAPSHOT.jar
RULES=$1
LOG_DIR=$2

# Change heap space limits with
# export JAVA_OPTS="-Xms16g -Xmx24g"

# Print GC statistics with
# export JAVA_OPTS="-XX:-PrintGC -XX:-PrintGCDetails"
# https://stackoverflow.com/a/466919

# Profile using VisualVM

mkdir -p $LOG_DIR

PROBLEM_NAME=${RULES%/op*}
PROBLEM_NAME=${PROBLEM_NAME##*/}

op_num=${RULES%.rules.small.dl}
num=${op_num##*op}

timeout --foreground --kill-after=600 600 scala $JAR_NAME --dtgs $RULES \
  > $LOG_DIR/${PROBLEM_NAME}_$num.out \
  2> $LOG_DIR/${PROBLEM_NAME}_$num.log

export RETURN_RESULT=$?
if [[ $RETURN_RESULT -eq 124 ]]; then
  query=`cat $LOG_DIR/${PROBLEM_NAME}_$num.out | tail -n -3`
  if [[ $query == *"SELECT"* ]]; then
    echo "$query"
    exit 0
  else
    echo Interrupted
    exit 1
  fi
elif [[ $RETURN_RESULT -ne 0 ]]; then
  query=`cat $LOG_DIR/${PROBLEM_NAME}_$num.out | tail -n -3`
  if [[ $query == *"SELECT"* ]]; then
    echo "$query"
    exit 0
  else
    echo Exited with error!
    exit 2
  fi
else
  query=`cat $LOG_DIR/${PROBLEM_NAME}_$num.out | tail -n -3`
  echo "$query"
  exit 0
fi
