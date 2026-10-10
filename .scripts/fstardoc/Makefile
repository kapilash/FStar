ALL_FSTs := $(wildcard tests/*.fst)
ALL_FSTIs := $(wildcard tests/*.fsti)
ALL_EXPECT := $(patsubst %,%.expect.md,$(ALL_FSTs) $(ALL_FSTIs))
ALL_GEN := $(patsubst %,%.gen.md,$(ALL_FSTs) $(ALL_FSTIs))
ALL_DIFF := $(patsubst %,%-diff,$(ALL_FSTs) $(ALL_FSTIs))

all: regression-tests fixtures unit-tests

unit-tests:
	@python3 test_ulib_docs.py -q
	@echo 'Test "unit-tests" passed.'

regression-tests: $(ALL_DIFF)

# The doc lint accepts every fixture in fixtures/valid and rejects every
# fixture in fixtures/invalid.
fixtures:
	@python3 ulib_docs.py lint-file fixtures/valid/*.md
	@for f in fixtures/invalid/*.md; do \
	  if python3 ulib_docs.py lint-file $$f > /dev/null; then \
	    echo "lint accepted $$f"; exit 1; fi; \
	done
	@echo 'Test "fixtures" passed.'

.PHONY: fixtures unit-tests

%.expect.md: %
	@touch $@

%.gen.md: % %.expect.md fstardoc.py
	@python3 fstardoc.py $< > $@

%-diff: %.expect.md %.gen.md
	@diff -u $^ && echo 'Test "$*" passed.'

update-to-latest:
	@echo "Cloning from base"
	@git clone --depth=1 https://github.com/jaybosamiya/fstardoc
	@echo "Copying over"
	@cp -r fstardoc/* .
	@echo "Cleaning up"
	@rm -rf fstardoc
	@git checkout -- README.md
	@echo "Done. Updates in this directory:"
	@git status .

.PRECIOUS: $(ALL_GEN) $(ALL_EXPECT)
