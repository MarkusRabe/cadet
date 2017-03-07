#!/usr/bin/env bash

./bloqqer $1 | ./caqe
exit_code=$?
exit $exit_code
