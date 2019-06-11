pipeline {
  agent none
  options {
    ansiColor('xterm')
    skipDefaultCheckout()
  }
  stages {
    stage('Kill old builds') {
      agent none
      when { changeRequest() }
      steps {
        script {
          def jobName     = env.JOB_NAME
          def buildNumber = env.BUILD_NUMBER.toInteger()
          def currentJobs = Jenkins.instance.getItemByFullName(jobName)
          for (def build : currentJobs.builds) {
            if (build.isBuilding() && build.number.toInteger() != buildNumber) {
              build.doStop()
            }
          }
        }
      }
    }
    stage('Init Title and Checkout') {
      agent { label 'docker' }
      stages {
        stage('Init title') {
          when { changeRequest() }
          steps {
            script {
              currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}"
            }
          }
        }
        stage('Checkout') {
          steps {
            checkout scm
          }
        }
      }
    }
    stage('Run CI') {
      agent {
        dockerfile {
          additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
          args '-m 60g'
          reuseNode true
        }
      }
      stages {
        stage('Dependencies') {
          steps {
            sh '''
              export PATH=$HOME/.local/bin:$HOME/.cargo/bin:$PATH
              make all-deps -B
              make split-tests -B
            '''
          }
        }
        stage('Build') {
          steps {
            sh '''
              export PATH=$HOME/.local/bin:$HOME/.cargo/bin:$PATH
              make build build-llvm build-haskell build-node -j4 -B
            '''
          }
        }
        stage('Test Execution') {
          failFast true
          parallel {
            stage('Conformance (OCaml)') {
              steps {
                sh '''
                  export PATH=$HOME/.local/bin:$PATH
                  nprocs=$(nproc)
                  make test-conformance -j"$nprocs" TEST_CONCRETE_BACKEND=ocaml
                '''
              }
            }
            stage('Conformance (LLVM)') {
              steps {
                sh '''
                  export PATH=$HOME/.local/bin:$PATH
                  nprocs=$(nproc)
                  make test-conformance -j"$nprocs" TEST_CONCRETE_BACKEND=llvm
                '''
              }
            }
          }
        }
        stage('Test Proofs (Java)') {
          options {
            lock("proofs-${env.NODE_NAME}")
          }
          steps {
            sh '''
              export PATH=$HOME/.local/bin:$PATH
              nprocs=$(nproc)
              [ "$nprocs" -gt '6' ] && nprocs='6'
              make test-proof -j"$nprocs"
            '''
          }
        }
        stage('Test Interactive') {
          failFast true
          parallel {
            stage('OCaml krun') {
              steps {
                sh '''
                  export PATH=$HOME/.local/bin:$PATH
                  make test-interactive-run TEST_CONCRETE_BACKEND=ocaml
                '''
              }
            }
            stage('LLVM krun') {
              steps {
                sh '''
                  export PATH=$HOME/.local/bin:$PATH
                  make test-interactive-run TEST_CONCRETE_BACKEND=llvm
                '''
              }
            }
            stage('Java krun') {
              steps {
                sh '''
                  export PATH=$HOME/.local/bin:$PATH
                  make test-interactive-run TEST_CONCRETE_BACKEND=java
                '''
              }
            }
            stage('Haskell krun') {
              steps {
                sh '''
                  export PATH=$HOME/.local/bin:$PATH
                  make test-interactive-run TEST_CONCRETE_BACKEND=haskell
                '''
              }
            }
            stage('OCaml kast') {
              steps {
                sh '''
                  export PATH=$HOME/.local/bin:$PATH
                  make test-parse TEST_CONCRETE_BACKEND=ocaml
                '''
              }
            }
            stage('Java KLab') {
              steps {
                sh '''
                  export PATH=$HOME/.local/bin:$PATH
                  make test-klab-prove TEST_SYMBOLIC_BACKEND=java
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
  }
}
