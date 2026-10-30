# Benchmark data checks only; build, verify and evaluate tasks with the root
# integration targets (`make -C ../../.. build-task|test-task|check-task TASK=<task-id>`).

.PHONY: test test-unit test-integration test-final build-coreutils clean

test:
	@$(MAKE) --no-print-directory test-unit

test-unit:
	@python3 -m pytest -c pytest-dev.ini -q

test-integration:
	@python3 -m pytest -c pytest-dev.ini -q -m integration

test-final:
	@$(MAKE) --no-print-directory test-unit && $(MAKE) --no-print-directory test-integration

build-coreutils:
	@tools/build-coreutils

clean:
	@test "$(abspath $(or $(BUILD_DIR),_build))" = "$(CURDIR)/_build" || \
		{ echo 'clean only removes the default _build directory' >&2; exit 2; }
	rm -rf -- "$(CURDIR)/_build"

# Release maintenance only; these tools never change task delivery or grading.
.PHONY: public-input-lock public-input-lint
public-input-lock:
	@python3 -m tools.public_inputs.cli lock $(if $(TASK),--task $(TASK))

public-input-lint:
	@python3 -m tools.public_inputs.cli lint $(if $(TASK),--task $(TASK))
