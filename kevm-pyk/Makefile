UV     := uv
UV_RUN := $(UV) run --


default: check test-unit

all: check cov

.PHONY: clean
clean:
	rm -rf dist .coverage cov-* .mypy_cache .pytest_cache
	find -type d -name __pycache__ -prune -exec rm -rf {} \;

.PHONY: build
build:
	$(UV) build


# Tests

PYTEST_BASE_ARGS := --verbose --durations=0 --dist=worksteal
PYTEST_ARGS      :=
PYTEST_PARALLEL  := 8
PYTEST_MAXFAIL   := 1

test: test-all

.PHONY: test-all
test-all:
	$(UV_RUN) pytest src/tests $(PYTEST_BASE_ARGS) --maxfail=$(PYTEST_MAXFAIL) --numprocesses=$(PYTEST_PARALLEL) $(PYTEST_ARGS)

.PHONY: test-unit
test-unit:
	$(UV_RUN) pytest src/tests/unit $(PYTEST_BASE_ARGS) --maxfail=$(PYTEST_MAXFAIL) --numprocesses=$(PYTEST_PARALLEL) $(PYTEST_ARGS)

.PHONY: test-integration
test-integration:
	$(UV_RUN) pytest src/tests/integration $(PYTEST_BASE_ARGS) --maxfail=$(PYTEST_MAXFAIL) --numprocesses=$(PYTEST_PARALLEL) $(PYTEST_ARGS)


# Coverage

COV_ARGS :=

cov: cov-all

cov-%: TEST_ARGS += --cov=kevm_pyk --no-cov-on-fail --cov-branch --cov-report=term

cov-all: TEST_ARGS += --cov-report=html:cov-all-html $(COV_ARGS)
cov-all: test-all

cov-unit: TEST_ARGS += --cov-report=html:cov-unit-html $(COV_ARGS)
cov-unit: test-unit

cov-integration: TEST_ARGS += --cov-report=html:cov-integration-html $(COV_ARGS)
cov-integration: test-integration


# Profiling

PROF_ARGS :=

.PHONY: profile
profile:
	$(UV_RUN) pytest src/tests/profiling --maxfail=1 --verbose --durations=0 --numprocesses=4 --dist=worksteal $(PROF_ARGS)


# Checks and formatting

format: autoflake isort black
check: check-flake8 check-mypy check-autoflake check-isort check-black

# Repo-root scripts/ are linted with the same config as src.  black and isort
# discover config relative to each target path, so they need an explicit config
# path to apply this pyproject's style to files outside the package tree.
SCRIPTS := ../scripts

.PHONY: check-flake8
check-flake8:
	$(UV_RUN) flake8 src $(SCRIPTS)

.PHONY: check-mypy
check-mypy:
	$(UV_RUN) mypy src $(SCRIPTS)

.PHONY: autoflake
autoflake:
	$(UV_RUN) autoflake --quiet --in-place src
	$(UV_RUN) autoflake --quiet --recursive --in-place $(SCRIPTS)

.PHONY: check-autoflake
check-autoflake:
	$(UV_RUN) autoflake --quiet --check src
	$(UV_RUN) autoflake --quiet --recursive --check $(SCRIPTS)

.PHONY: isort
isort:
	$(UV_RUN) isort --settings-path pyproject.toml src $(SCRIPTS)

.PHONY: check-isort
check-isort:
	$(UV_RUN) isort --check --settings-path pyproject.toml src $(SCRIPTS)

.PHONY: black
black:
	$(UV_RUN) black --config pyproject.toml src $(SCRIPTS)

.PHONY: check-black
check-black:
	$(UV_RUN) black --check --config pyproject.toml src $(SCRIPTS)


# Optional tools

SRC_FILES := $(shell find src -type f -name '*.py')

.PHONY: pyupgrade
pyupgrade:
	$(UV_RUN) pyupgrade --py310-plus $(SRC_FILES)
