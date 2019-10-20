pipeline {
  agent none
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
        }
      }
      stages {
        stage('Dependencies') {
          steps {
            sh '''
              make deps ocaml-deps split-tests -j3
            '''
          }
        }
        stage('Build') {
          steps {
            sh '''
              make build-all -j4
            '''
          }
        }
        stage('Test Execution') {
          failFast true
          options { timeout(time: 15, unit: 'MINUTES') }
          parallel {
            stage('Conformance (OCaml)') {
              steps {
                sh '''
                  make test-conformance -j8 TEST_CONCRETE_BACKEND=ocaml
                '''
              }
            }
            stage('Conformance (LLVM)') {
              steps {
                sh '''
                  make test-conformance -j8 TEST_CONCRETE_BACKEND=llvm
                '''
              }
            }
            stage('Conformance (Web3)') {
              steps {
                sh '''
                  make test-web3
                '''
              }
            }
          }
        }
        stage('Proofs') {
          options {
            lock("proofs-${env.NODE_NAME}")
            timeout(time: 60, unit: 'MINUTES')
          }
          parallel {
            stage('Java') {
              steps {
                sh '''
                  make test-prove -j6
                '''
              }
            }
            stage('Haskell') {
              steps {
                sh '''
                  make tests/specs/examples/sum-to-n-spec.k.prove TEST_SYMBOLIC_BACKEND=haskell
                '''
              }
            }
          }
        }
        stage('Test Interactive') {
          failFast true
          options { timeout(time: 35, unit: 'MINUTES') }
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
            stage('Firefly') {
              steps {
                sh '''
                  export PATH=$PATH:$(pwd)/.build/defn/vm
                  make test-interactive-firefly
                '''
              }
            }
          }
        }
      }
    }
    stage('Release') {
      agent { label 'docker' }
      options { skipDefaultCheckout() }
      environment {
        GITHUB_TOKEN    = credentials('rv-jenkins')
        KEVM_RELEASE_ID = '1.0.0'
        PACKAGE = 'kevm'
        VERSION = '1.0.0'
        ROOT_URL = 'https://github.com/kframework/evm-semantics/releases/download/nightly'
      }
      stages {
        stage('Test Release') {
          stages {
            stage('Checkout SCM - Download K Release') {
              steps {
                dir("kevm-${env.KEVM_RELEASE_ID}") {
                  checkout scm
                  sh '''
                    commit_short=$(cd deps/k && git rev-parse --short HEAD)
                    K_RELEASE="https://github.com/kframework/k/releases/download/nightly-$commit_short"
                    curl --fail --location "${K_RELEASE}/kframework_5.0.0_amd64_bionic.deb"    --output kframework-bionic.deb
                    curl --fail --location "${K_RELEASE}/kframework-5.0.0-1-x86_64.pkg.tar.xz" --output kframework-git.pkg.tar.xz
                    curl --fail --location "${K_RELEASE}/kframework_5.0.0_amd64_buster.deb"    --output kframework-buster.deb
                  '''
                  stash name: 'bionic-kframework', includes: 'kframework-bionic.deb'
                  stash name: 'buster-kframework', includes: 'kframework-buster.deb'
                  stash name: 'arch-kframework',   includes: 'kframework-git.pkg.tar.xz'
                }
              }
            }
            stage('Build Ubuntu Bionic Package') {
              agent {
                dockerfile {
                  dir "kevm-${env.KEVM_RELEASE_ID}/package"
                  filename 'Dockerfile.ubuntu-bionic'
                  additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
                  reuseNode true
                }
              }
              steps {
                dir("kevm-${env.KEVM_RELEASE_ID}") {
                  checkout scm
                  unstash 'bionic-kframework'
                  sh '''
                    sudo apt-get update && sudo apt-get upgrade --yes
                    sudo apt-get install --yes ./kframework-bionic.deb
                    cp -r package/debian ./
                    cp package/ubuntu/* debian
                    dpkg-buildpackage --no-sign
                  '''
                }
                stash name: 'bionic-kevm', includes: "kevm_${env.KEVM_RELEASE_ID}_amd64.deb"
              }
            }
            stage('Test Ubuntu Bionic Package') {
              options { timeout(time: 15, unit: 'MINUTES') }
              agent {
                dockerfile {
                  dir "kevm-${env.KEVM_RELEASE_ID}/package"
                  filename 'Dockerfile.ubuntu-bionic'
                  additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
                  reuseNode true
                }
              }
              steps {
                dir("kevm-${env.KEVM_RELEASE_ID}") {
                  unstash 'bionic-kevm'
                  sh '''
                    sudo apt-get update && sudo apt-get upgrade --yes
                    sudo apt-get install --yes ./kevm_${KEVM_RELEASE_ID}_amd64.deb
                    export PATH=$PATH:$(pwd)/.build/defn/vm
                    make test-interactive-firefly
                  '''
                }
              }
            }
          }
        }
        stage('Deploy Release') {
          //when {
          //  not { changeRequest() }
          //  branch 'master'
          //  beforeAgent true
          //}
          stages {
            stage('Build Source Tarball') {
              agent {
                dockerfile {
                  dir "kevm-${env.KEVM_RELEASE_ID}/package"
                  filename 'Dockerfile.arch'
                  additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
                  reuseNode true
                }
              }
              steps {
                dir("kevm-${KEVM_RELEASE_ID}-src") {
                  checkout scm
                  sh '''
                    find . -name .git | xargs rm -r
                    rm -r deps/k tests/ethereum-tests deps/metropolis
                    cd ..
                    tar czvf kevm-${KEVM_RELEASE_ID}-src.tar.gz kevm-${KEVM_RELEASE_ID}-src
                  '''
                }
                stash name: 'src-kevm', includes: "kevm-${env.KEVM_RELEASE_ID}-src.tar.gz"
              }
            }
            stage('Build Debian Buster Package') {
              agent {
                dockerfile {
                  dir "kevm-${env.KEVM_RELEASE_ID}/package"
                  filename 'Dockerfile.debian-buster'
                  additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
                  reuseNode true
                }
              }
              steps {
                dir("kevm-${env.KEVM_RELEASE_ID}") {
                  checkout scm
                  unstash 'buster-kframework'
                  sh '''
                    sudo apt-get update && sudo apt-get upgrade --yes
                    sudo apt-get install --yes ./kframework-buster.deb
                    cp -r package/debian ./
                    dpkg-buildpackage --no-sign
                  '''
                }
                stash name: 'buster-kevm', includes: "kevm_${env.KEVM_RELEASE_ID}_amd64.deb"
              }
            }
            stage('Test Debian Buster Package') {
              options { timeout(time: 15, unit: 'MINUTES') }
              agent {
                dockerfile {
                  dir "kevm-${env.KEVM_RELEASE_ID}/package"
                  filename 'Dockerfile.debian-buster'
                  additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
                  reuseNode true
                }
              }
              steps {
                dir("kevm-${env.KEVM_RELEASE_ID}") {
                  unstash 'buster-kevm'
                  sh '''
                    sudo apt-get update && sudo apt-get upgrade --yes
                    sudo apt-get install --yes ./kevm_${KEVM_RELEASE_ID}_amd64.deb
                    export PATH=$PATH:$(pwd)/.build/defn/vm
                    make test-interactive-firefly
                  '''
                }
              }
            }
            stage('Build Homebrew Bottle') {
              agent {
                label 'anka'
              }
              steps {
                unstash 'src-kevm'
                dir('homebrew-k') {
                  git url: 'git@github.com:kframework/homebrew-k.git'
                  sh '''
                    ${WORKSPACE}/deps/k/src/main/scripts/brew-build-bottle
                  '''
                  stash name: "mojave-kevm", includes: "kevm--${env.KEVM_RELEASE_ID}.mojave.bottle*.tar.gz"
                }
              }
            }
            stage('Test Homebrew Bottle') {
              agent {
                label 'anka'
              }
              steps {
                dir('homebrew-k') {
                  git url: 'git@github.com:kframework/homebrew-k.git', branch: 'brew-release-kevm'
                  unstash "mojave-kevm"
                  sh '''
                    ${WORKSPACE}/deps/k/src/main/scripts/brew-install-bottle
                  '''
                }
                dir("kevm-${env.KEVM_RELEASE_ID}") {
                  checkout scm
                  sh '''
                    brew install node@10 netcat
                    export PATH="/usr/local/opt/node@10/bin:$PATH"
                    npm install -g npx
                    make test-interactive-firefly
                  '''
                }
                dir('homebrew-k') {
                  sh '''
                    ${WORKSPACE}/deps/k/src/main/scripts/brew-update-to-final
                  '''
                }
              }
            }
            // stage('Build Arch Package') {
            //   agent {
            //     dockerfile {
            //       dir "kevm-${env.KEVM_RELEASE_ID}/package"
            //       filename 'Dockerfile.arch'
            //       additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
            //       reuseNode true
            //     }
            //   }
            //   steps {
            //     dir("kevm-${env.KEVM_RELEASE_ID}") {
            //       checkout scm
            //       unstash 'arch-kframework'
            //       sh '''
            //         sudo pacman -Syu --noconfirm
            //         sudo pacman --noconfirm -U kframework-git.pkg.tar.xz
            //         cd package
            //         makepkg --noconfirm --syncdeps
            //       '''
            //     }
            //     stash name: 'arch-kevm', includes: "kevm-${env.KEVM_RELEASE_ID}/package/kevm-git-${env.KEVM_RELEASE_ID}-1-x86_64.pkg.tar.xz"
            //   }
            // }
            // stage('Test Arch Package') {
            //   options { timeout(time: 15, unit: 'MINUTES') }
            //   agent {
            //     dockerfile {
            //       dir "kevm-${env.KEVM_RELEASE_ID}/package"
            //       filename 'Dockerfile.arch'
            //       additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
            //       reuseNode true
            //     }
            //   }
            //   steps {
            //     dir("kevm-${env.KEVM_RELEASE_ID}") {
            //       unstash 'arch-kevm'
            //       sh '''
            //         sudo pacman -Syu --noconfirm
            //         sudo pacman --noconfirm -U package/kevm-git-${KEVM_RELEASE_ID}-1-x86_64.pkg.tar.xz
            //         export PATH=$PATH:$(pwd)/.build/defn/vm
            //         make test-interactive-firefly
            //       '''
            //     }
            //   }
            // }
            stage('Upload Release') {
              agent {
                dockerfile {
                  dir "kevm-${env.KEVM_RELEASE_ID}/package"
                  filename 'Dockerfile.arch'
                  additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
                  reuseNode true
                }
              }
              steps {
                dir("kevm-${env.KEVM_RELEASE_ID}") {
                  unstash 'src-kevm'
                  dir("bionic") {
                    unstash 'bionic-kevm'
                  }
                  dir("buster") {
                    unstash 'buster-kevm'
                  }
                  dir("mojave") {
                    unstash 'mojave-kevm'
                  }
                  // dir("arch") {
                  //   unstash 'arch-kevm'
                  // }
                  sh '''
                    release_tag="v${KEVM_RELEASE_ID}-$(git rev-parse --short HEAD)"
                    make release.md KEVM_RELEASE_TAG=${release_tag}
                    mv bionic/kevm_${KEVM_RELEASE_ID}_amd64.deb bionic/kevm_${KEVM_RELEASE_ID}_amd64_bionic.deb
                    mv buster/kevm_${KEVM_RELEASE_ID}_amd64.deb buster/kevm_${KEVM_RELEASE_ID}_amd64_buster.deb
                    hub release create                                                                                               \
                        --attach "kevm-${KEVM_RELEASE_ID}-src.tar.gz#Source tar.gz"                                                  \
                        --attach "bionic/kevm_${KEVM_RELEASE_ID}_amd64_bionic.deb#Ubuntu Bionic (18.04) Package"                     \
                        --attach "buster/kevm_${KEVM_RELEASE_ID}_amd64_buster.deb#Debian Buster (10) Package"                        \
                        --attach "mojave/kevm--${KEVM_RELEASE_ID}.mojave.bottle*.tar.gz#Mac OS X Homebrew Bottle"                    \
                        --file "release.md" "${release_tag}"
                        # --attach "arch/kevm-${KEVM_RELEASE_ID}/package/kevm-git-${KEVM_RELEASE_ID}-1-x86_64.pkg.tar.xz#Arch Package" \
                  '''
                }
              }
            }
          }
        }
      }
      post {
        failure {
          slackSend color: '#cb2431'                                 \
                  , channel: '#kevm'                                 \
                  , message: "KEVM Release Failed: ${env.BUILD_URL}"
        }
      }
    }
  }
}
