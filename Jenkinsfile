pipeline {
  agent {
    dockerfile {
      additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
      args '-m 60g'
    }
  }
  options {
    ansiColor('xterm')
  }
  stages {
    stage("Init title") {
      when { changeRequest() }
      steps {
        script {
          currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}"
        }
      }
    }
    stage('Dependencies') {
      steps {
        sh '''
          make all-deps -B
          make split-tests -B
        '''
      }
    }
    stage('Build') {
      steps {
        sh '''
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
              nprocs=$(nproc)
              make test-conformance -j"$nprocs" TEST_CONCRETE_BACKEND=ocaml
            '''
          }
        }
        stage('Conformance (LLVM)') {
          steps {
            sh '''
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
              make test-interactive-run TEST_CONCRETE_BACKEND=ocaml
            '''
          }
        }
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
        stage('OCaml kast') {
          steps {
            sh '''
              make test-parse TEST_CONCRETE_BACKEND=ocaml
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
