pipeline {
  agent {
    dockerfile {
      additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
      args '-m 60g'
    }
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
    stage('Build') {
      steps {
        ansiColor('xterm') {
          sh '''
            export PATH=$HOME/.local/bin:$HOME/.cargo/bin:$PATH
            make llvm-deps   -B
            make build       -B -j4
            make build-llvm
            make split-tests -B
          '''
        }
      }
    }
    stage('Test Execution') {
      failFast true
      parallel {
        stage('Conformance') {
          steps {
            ansiColor('xterm') {
              sh '''
                export PATH=$HOME/.local/bin:$PATH
                nprocs=$(nproc)
                make test-concrete -j"$nprocs"
              '''
            }
          }
        }
        stage('Conformance (LLVM)') {
          steps {
            ansiColor('xterm') {
              sh '''
                export PATH=$HOME/.local/bin:$PATH
                nprocs=$(nproc)
                make TEST_CONCRETE_BACKEND=llvm test-concrete -j"$nprocs"
              '''
            }
          }
        }
      }
    }
    stage('Test Proofs') {
      options {
        lock("proofs-${env.NODE_NAME}")
      }
      steps {
        ansiColor('xterm') {
          sh '''
            export PATH=$HOME/.local/bin:$PATH
            nprocs=$(nproc)
            [ "$nprocs" -gt '6' ] && nprocs='6'
            make test-proof -j"$nprocs"
          '''
        }
      }
    }
  }
}
