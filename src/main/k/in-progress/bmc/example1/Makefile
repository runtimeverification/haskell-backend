DEFINITION_NAME := bmc

include $(CURDIR)/../../../working/include.mk

BMC_FAIL_TEST := fail/test1-spec.20 \
                 fail/test2-spec.20 \
                 fail/test3-spec.20 \
                 fail/test4-spec.20

BMC_SUCCESS_TEST := success/test1-spec.20 \
                    success/test2-spec.10 \

BMC_UNKNOWN_TEST := success/test3-spec.20

BMC_TEST := $(BMC_FAIL_TEST) \
            $(BMC_SUCCESS_TEST) \
            $(BMC_UNKNOWN_TEST)

test-bmc: $(foreach test, $(BMC_TEST), $(test).kbmc.test)

clean:
	rm -rf $(KOMPILED) fail/*.output success/*.output

.PHONY: test-bmc clean
