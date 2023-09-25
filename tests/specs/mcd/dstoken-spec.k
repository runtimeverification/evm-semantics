requires "dstoken-approve-fail-rough-spec.k"
requires "dstoken-burn-self-fail-rough-spec.k"
requires "dstoken-move-pass-spec.k"
requires "dstoken-transferfrom-fail-rough-spec.k"
requires "dstoken-transfer-pass-spec.k"

module DSTOKEN-SPEC
    imports DSTOKEN-APPROVE-FAIL-ROUGH-SPEC
    imports DSTOKEN-BURN-SELF-FAIL-ROUGH-SPEC
    imports DSTOKEN-MOVE-PASS-SPEC
    imports DSTOKEN-TRANSFER-SPEC
    imports DSTOKEN-TRANSFERFROM-FAIL-ROUGH-SPEC
endmodule
