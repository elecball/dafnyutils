.PHONY: build build-dafny build-image test test-unit test-integration test-final check check-environment build-coreutils clean

build:
	@python3 -m benchmarks.make_tasks build --task "$(TASK)"

build-dafny:
	dotnet build dafny/Source/Dafny.sln --no-incremental \
		-p:PathMap="$(CURDIR)/dafny=/src/dafny" \
		-p:ContinuousIntegrationBuild=true \
		-p:Deterministic=true

build-image:
	@python3 -m tools.build_image

test:
ifneq ($(strip $(TASK)),)
	@python3 -m benchmarks.make_tasks test --task "$(TASK)"
else
	@$(MAKE) --no-print-directory test-unit
endif

test-unit:
	@python3 -m pytest -c pytest-dev.ini -q

test-integration:
	@python3 -m pytest -c pytest-dev.ini -q -m integration

test-final:
	@$(MAKE) --no-print-directory test-unit && $(MAKE) --no-print-directory test-integration

check:
	@test -n "$$TASK" || { echo 'TASK=<task-id> is required' >&2; exit 2; }
	@python3 -m benchmarks check "$$TASK"

build-coreutils:
	@tools/build-coreutils

check-environment:
	@bash tools/check-contributor-env

clean:
	@test "$(abspath $(or $(BUILD_DIR),_build))" = "$(CURDIR)/_build" || \
		{ echo 'clean only removes the default _build directory' >&2; exit 2; }
	rm -rf -- "$(CURDIR)/_build"
