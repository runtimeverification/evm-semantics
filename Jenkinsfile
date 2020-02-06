pipeline {
  agent none
  environment {
    GITHUB_TOKEN = credentials('rv-jenkins')
    VERSION      = '1.0.0'
    K_VERSION    = '5.0.0'
    K_ROOT_URL   = 'https://github.com/kframework/k/releases/download'
    PACKAGE      = 'kevm'
    ROOT_URL     = 'https://github.com/kframework/evm-semantics/releases/download'
  }
  options {
    ansiColor('xterm')
  }
  stages {
    stage("Init title") {
      when {
        changeRequest()
        beforeAgent true
      }
      steps {
        script {
          currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}"
        }
      }
    }
    stage('Build and Test') {
      when {
        changeRequest()
        beforeAgent true
      }
      agent {
        dockerfile {
          additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
          args '-m 60g'
          label 'docker && !smol'
        }
      }
      stages {
        stage('Dependencies') {
          parallel {
            stage('K') {
              steps {
                sh '''
                  make deps
                '''
              }
            }
            stage('Tests') {
              steps {
                sh '''
                  make split-tests -j3
                '''
              }
            }
          }
        }
        stage('Build') {
          steps {
            sh '''
              make build -j4
            '''
          }
        }
        stage('Test Execution') {
          failFast true
          options { timeout(time: 50, unit: 'MINUTES') }
          parallel {
            stage('Conformance (LLVM)') {
              steps {
                sh '''
                  make test-conformance -j8 TEST_CONCRETE_BACKEND=llvm
                '''
              }
            }
            stage('VM (Haskell)') {
              steps {
                sh '''
                  make test-vm -j8 TEST_CONCRETE_BACKEND=haskell
                '''
              }
            }
            stage('Conformance (Web3)') {
              steps {
                sh '''
                  make test-web3 -j8
                '''
              }
            }
            stage('Conformance (Truffle)') {
              steps {
                sh '''
                  make test-truffle
                  make test-openzep
                  make test-synthetix
                '''
              }
            }
          }
        }
        stage('Proofs') {
          options {
            lock("proofs-${env.NODE_NAME}")
            timeout(time: 55, unit: 'MINUTES')
          }
          parallel {
            stage('Java + Haskell') {
              steps {
                sh '''
                  make test-prove -j6
                '''
              }
            }
            stage('Haskell (dry-run)') {
              steps {
                sh '''
                  make test-prove -j2 KPROVE_OPTIONS='--dry-run' TEST_SYMBOLIC_BACKEND='haskell'
                '''
              }
            }
          }
        }
        stage('Test Interactive') {
          failFast true
          options { timeout(time: 35, unit: 'MINUTES') }
          parallel {
            stage('LLVM krun') {
              steps {
                sh '''
                  make test-interactive-run TEST_CONCRETE_BACKEND=llvm
                '''
              }
            }
            stage('Java krun') {
              steps {
                sh '''
                  make test-interactive-run TEST_CONCRETE_BACKEND=java
                '''
              }
            }
            stage('Haskell krun') {
              steps {
                sh '''
                  make test-interactive-run TEST_CONCRETE_BACKEND=haskell
                '''
              }
            }
            stage('LLVM Kast') {
              steps {
                sh '''
                  make test-parse TEST_CONCRETE_BACKEND=llvm
                '''
              }
            }
            stage('Failing tests') {
              steps {
                sh '''
                  make test-failure TEST_CONCRETE_BACKEND=llvm
                '''
              }
            }
            stage('Java KLab') {
              steps {
                sh '''
                  make test-klab-prove TEST_SYMBOLIC_BACKEND=java
                '''
              }
            }
            stage('Haskell Search') {
              steps {
                sh '''
                  make test-interactive-search TEST_SYMBOLIC_BACKEND=haskell -j4
                '''
              }
            }
            stage('KEVM help') {
              steps {
                sh '''
                  ./kevm help
                '''
              }
            }
          }
        }
      }
    }
    stage('Update Dependents') {
      when { branch 'master' }
      steps {
        build job: 'rv-devops/master', propagate: false, wait: false                                     \
            , parameters: [ booleanParam(name: 'UPDATE_DEPS_SUBMODULE', value: true)                     \
                          , string(name: 'PR_REVIEWER', value: 'ehildenb')                               \
                          , string(name: 'UPDATE_DEPS_REPOSITORY', value: 'runtimeverification/firefly') \
                          , string(name: 'UPDATE_DEPS_SUBMODULE_DIR', value: 'deps/evm-semantics')       \
                          ]
        build job: 'rv-devops/master', propagate: false, wait: false                                                \
            , parameters: [ booleanParam(name: 'UPDATE_DEPS_SUBMODULE', value: true)                                \
                          , string(name: 'PR_REVIEWER', value: 'ehildenb')                                          \
                          , string(name: 'UPDATE_DEPS_REPOSITORY', value: 'runtimeverification/erc20-verification') \
                          , string(name: 'UPDATE_DEPS_SUBMODULE_DIR', value: 'deps/evm-semantics')                  \
                          ]
      }
    }
  }
}
