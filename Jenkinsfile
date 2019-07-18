pipeline {
  agent none
  options {
    ansiColor('xterm')
  }
  stages {
    stage('Build and Test') {
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
                  [ "$nprocs" -gt '16' ] && nprocs='16'
                  make test-conformance -j"$nprocs" TEST_CONCRETE_BACKEND=ocaml
                '''
              }
            }
            stage('Conformance (LLVM)') {
              steps {
                sh '''
                  nprocs=$(nproc)
                  [ "$nprocs" -gt '16' ] && nprocs='16'
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
            stage('Failing tests') {
              steps {
                sh '''
                  make test-failure TEST_CONCRETE_BACKEND=ocaml
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
    stage('Deploy') {
      // when {
      //   not { changeRequest() }
      //   branch 'master'
      //   beforeAgent true
      // }
      environment {
        GITHUB_TOKEN = credentials('rv-jenkins')
        RELEASE_ID   = '0.0.1'
      }
      stages {
        stage('Build Ubuntu Package') {
          agent {
            dockerfile {
              dir 'package'
              filename 'Dockerfile.ubuntu-bionic'
            }
          }
          steps {
            sh '''
              curl --location --output k-nightly-bionic.deb "https://github.com/kframework/k/releases/download/nightly-89361d7c8/kframework_5.0.0_amd64_bionic.deb"
              sudo apt install --yes ./k-nightly-bionic.deb
              dpkg-buildpackage --no-sign
              sudo apt install ../kevm_"$RELEASE_ID"_amd64.deb
            '''
            stash name: 'bionic', includes: "kevm_${env.RELEASE_ID}_amd64.deb"
          }
        }
        stage('Upload Packages') {
          when { branch 'master' }
          agent {
            dockerfile {
              dir 'package'
              filename 'Dockerfile.arch'
            }
          }
          steps {
            unstash 'bionic'
            sh '''
              commit_hash_full=$(git rev-parse HEAD)
              commit_hash_8=$(echo $commit_hash_full | cut --characters=1-8)
              hub release create --attach README.md --message "$(echo -e "KEVM Release\n" ; cat INSTALL.md ;)" --target $(git rev-parse HEAD) "v$RELEASE_ID-$commit_hash_8"
            '''
          }
        }
      }
    }
  }
}
