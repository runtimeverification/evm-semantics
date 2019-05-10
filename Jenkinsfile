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
              make test-concrete -j"$nprocs"
            '''
          }
        }
        stage('Conformance (LLVM)') {
          steps {
            sh '''
              export PATH=$HOME/.local/bin:$PATH
              nprocs=$(nproc)
              make TEST_CONCRETE_BACKEND=llvm test-concrete -j"$nprocs"
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
        stage('OCaml') {
          steps {
            sh '''
              export PATH=$HOME/.local/bin:$PATH
              nprocs=$(nproc)
              make test-interactive TEST_CONCRETE_BACKEND=ocaml
            '''
          }
        }
        stage('LLVM') {
          steps {
            sh '''
              export PATH=$HOME/.local/bin:$PATH
              nprocs=$(nproc)
              make test-interactive TEST_CONCRETE_BACKEND=llvm
            '''
          }
        }
        stage('Java') {
          steps {
            sh '''
              export PATH=$HOME/.local/bin:$PATH
              nprocs=$(nproc)
              make test-interactive TEST_CONCRETE_BACKEND=java
            '''
          }
        }
        stage('Haskell') {
          steps {
            sh '''
              export PATH=$HOME/.local/bin:$PATH
              nprocs=$(nproc)
              make test-interactive TEST_CONCRETE_BACKEND=haskell
            '''
          }
        }
      }
    }
  }
}
