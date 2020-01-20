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
        }
      }
      stages {
        stage('Dependencies') {
          steps {
            sh '''
              make deps split-tests -j3
            '''
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
          options { timeout(time: 30, unit: 'MINUTES') }
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
                  make tests/openzeppelin-contracts/truffle-config.js
                  make test-truffle
                  make test-openzep
                '''
              }
            }
          }
        }
        stage('Proofs') {
          options {
            lock("proofs-${env.NODE_NAME}")
            timeout(time: 80, unit: 'MINUTES')
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
//    stage('Release') {
//      agent { label 'docker' }
//      options { skipDefaultCheckout() }
//      stages {
//        stage('Test Release') {
//          stages {
//            stage('Checkout SCM - Download K Release') {
//              steps {
//                dir("kevm-${env.VERSION}") {
//                  checkout scm
//                  sh '''
//                    k_commit_short=$(cd deps/k && git rev-parse --short HEAD)
//                    K_RELEASE="${K_ROOT_URL}/v${K_VERSION}-${k_commit_short}"
//                    curl --fail --location "${K_RELEASE}/kframework_${K_VERSION}_amd64_bionic.deb"        --output kframework-bionic.deb
//                    curl --fail --location "${K_RELEASE}/kframework_${K_VERSION}_amd64_buster.deb"        --output kframework-buster.deb
//                    # curl --fail --location "${K_RELEASE}/kframework-git-${K_VERSION}-1-x86_64.pkg.tar.xz" --output kframework-git.pkg.tar.xz
//                  '''
//                  stash name: 'bionic-kframework', includes: 'kframework-bionic.deb'
//                  stash name: 'buster-kframework', includes: 'kframework-buster.deb'
//                  // stash name: 'arch-kframework',   includes: 'kframework-git.pkg.tar.xz'
//                }
//              }
//            }
//            stage('Build Ubuntu Bionic Package') {
//              agent {
//                dockerfile {
//                  dir "kevm-${env.VERSION}/package"
//                  filename 'Dockerfile.ubuntu-bionic'
//                  additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
//                  reuseNode true
//                }
//              }
//              steps {
//                dir("kevm-${env.VERSION}") {
//                  checkout scm
//                  unstash 'bionic-kframework'
//                  sh '''
//                    sudo apt-get update && sudo apt-get upgrade --yes
//                    sudo apt-get install --yes ./kframework-bionic.deb
//                    cp -r package/debian ./
//                    cp package/ubuntu/* debian
//                    dpkg-buildpackage --no-sign
//                  '''
//                }
//                stash name: 'bionic-kevm', includes: "kevm_${env.VERSION}_amd64.deb"
//              }
//            }
//            stage('Test Ubuntu Bionic Package') {
//              options { timeout(time: 15, unit: 'MINUTES') }
//              agent {
//                dockerfile {
//                  dir "kevm-${env.VERSION}/package"
//                  filename 'Dockerfile.ubuntu-bionic'
//                  additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
//                  reuseNode true
//                }
//              }
//              steps {
//                dir("kevm-${env.VERSION}") {
//                  unstash 'bionic-kevm'
//                  sh '''
//                    sudo apt-get update && sudo apt-get upgrade --yes
//                    sudo apt-get install --yes ./kevm_${VERSION}_amd64.deb
//                    export PATH=$PATH:$(pwd)/.build/defn/vm
//                    make test-interactive-firefly
//                  '''
//                }
//              }
//            }
//          }
//        }
//        stage('Deploy Release') {
//          when {
//            branch 'master'
//            beforeAgent true
//          }
//          post {
//            failure {
//              slackSend color: '#cb2431'                                 \
//                      , channel: '#kevm'                                 \
//                      , message: "KEVM Release Failed: ${env.BUILD_URL}"
//            }
//          }
//          stages {
//            stage('Build Source Tarball') {
//              agent {
//                dockerfile {
//                  dir "kevm-${env.VERSION}/package"
//                  filename 'Dockerfile.arch'
//                  additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
//                  reuseNode true
//                }
//              }
//              steps {
//                dir("kevm-${env.VERSION}-src") {
//                  checkout scm
//                  sh '''
//                    find . -name .git | xargs rm -r
//                    rm -r deps/k tests/ethereum-tests deps/metropolis
//                    cd ..
//                    tar czvf kevm-${VERSION}-src.tar.gz kevm-${VERSION}-src
//                  '''
//                }
//                stash name: 'src-kevm', includes: "kevm-${env.VERSION}-src.tar.gz"
//              }
//            }
//            stage('Deploy Jello Paper') {
//              agent {
//                dockerfile {
//                  dir "kevm-${env.VERSION}"
//                  reuseNode true
//                }
//              }
//              steps {
//                sshagent(['2b3d8d6b-0855-4b59-864a-6b3ddf9c9d1a']) {
//                  dir("kevm-${env.VERSION}-jello-paper") {
//                    checkout scm
//                    sh '''
//                      git config --global user.email "admin@runtimeverification.com"
//                      git config --global user.name  "RV Jenkins"
//                      mkdir -p ~/.ssh
//                      echo 'host github.com'                       > ~/.ssh/config
//                      echo '    hostname github.com'              >> ~/.ssh/config
//                      echo '    user git'                         >> ~/.ssh/config
//                      echo '    identityagent SSH_AUTH_SOCK'      >> ~/.ssh/config
//                      echo '    stricthostkeychecking accept-new' >> ~/.ssh/config
//                      chmod go-rwx -R ~/.ssh
//                      ssh github.com || true
//                      git remote set-url origin 'ssh://github.com/kframework/evm-semantics'
//                      git checkout -B 'gh-pages'
//                      rm -rf .build .gitignore .gitmodules cmake deps Dockerfile Jenkinsfile kast-json.py kevm kore-json.py LICENSE Makefile media package
//                      git add ./
//                      git commit -m 'gh-pages: remove unrelated content'
//                      git fetch origin gh-pages
//                      git merge --strategy ours FETCH_HEAD
//                      git push origin gh-pages
//                    '''
//                  }
//                }
//              }
//            }
//            stage('Build Debian Buster Package') {
//              agent {
//                dockerfile {
//                  dir "kevm-${env.VERSION}/package"
//                  filename 'Dockerfile.debian-buster'
//                  additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
//                  reuseNode true
//                }
//              }
//              steps {
//                dir("kevm-${env.VERSION}") {
//                  checkout scm
//                  unstash 'buster-kframework'
//                  sh '''
//                    sudo apt-get update && sudo apt-get upgrade --yes
//                    sudo apt-get install --yes ./kframework-buster.deb
//                    cp -r package/debian ./
//                    dpkg-buildpackage --no-sign
//                  '''
//                }
//                stash name: 'buster-kevm', includes: "kevm_${env.VERSION}_amd64.deb"
//              }
//            }
//            stage('Test Debian Buster Package') {
//              options { timeout(time: 15, unit: 'MINUTES') }
//              agent {
//                dockerfile {
//                  dir "kevm-${env.VERSION}/package"
//                  filename 'Dockerfile.debian-buster'
//                  additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
//                  reuseNode true
//                }
//              }
//              steps {
//                dir("kevm-${env.VERSION}") {
//                  unstash 'buster-kevm'
//                  sh '''
//                    sudo apt-get update && sudo apt-get upgrade --yes
//                    sudo apt-get install --yes ./kevm_${VERSION}_amd64.deb
//                    export PATH=$PATH:$(pwd)/.build/defn/vm
//                    make test-interactive-firefly
//                  '''
//                }
//              }
//            }
//            stage('Build Homebrew Bottle') {
//              agent {
//                label 'anka'
//              }
//              steps {
//                unstash 'src-kevm'
//                dir('homebrew-k') {
//                  git url: 'git@github.com:kframework/homebrew-k.git'
//                  sh '''
//                    ${WORKSPACE}/deps/k/src/main/scripts/brew-build-bottle
//                  '''
//                  stash name: "mojave-kevm", includes: "kevm--${env.VERSION}.mojave.bottle*.tar.gz"
//                }
//              }
//            }
//            stage('Test Homebrew Bottle') {
//              agent {
//                label 'anka'
//              }
//              steps {
//                dir('homebrew-k') {
//                  git url: 'git@github.com:kframework/homebrew-k.git', branch: 'brew-release-kevm'
//                  unstash "mojave-kevm"
//                  sh '''
//                    ${WORKSPACE}/deps/k/src/main/scripts/brew-install-bottle
//                  '''
//                }
//                dir("kevm-${env.VERSION}") {
//                  checkout scm
//                  sh '''
//                    brew install node@10 netcat
//                    export PATH="/usr/local/opt/node@10/bin:$PATH"
//                    npm install -g npx
//                    make test-interactive-firefly
//                  '''
//                }
//                dir('homebrew-k') {
//                  sh '''
//                    ${WORKSPACE}/deps/k/src/main/scripts/brew-update-to-final
//                  '''
//                }
//              }
//            }
//            // stage('Build Arch Package') {
//            //   agent {
//            //     dockerfile {
//            //       dir "kevm-${env.VERSION}/package"
//            //       filename 'Dockerfile.arch'
//            //       additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
//            //       reuseNode true
//            //     }
//            //   }
//            //   steps {
//            //     dir("kevm-${env.VERSION}") {
//            //       checkout scm
//            //       unstash 'arch-kframework'
//            //       sh '''
//            //         sudo pacman -Syu --noconfirm
//            //         sudo pacman --noconfirm -U kframework-git.pkg.tar.xz
//            //         cd package
//            //         makepkg --noconfirm --syncdeps
//            //       '''
//            //     }
//            //     stash name: 'arch-kevm', includes: "kevm-${env.VERSION}/package/kevm-git-${env.VERSION}-1-x86_64.pkg.tar.xz"
//            //   }
//            // }
//            // stage('Test Arch Package') {
//            //   options { timeout(time: 15, unit: 'MINUTES') }
//            //   agent {
//            //     dockerfile {
//            //       dir "kevm-${env.VERSION}/package"
//            //       filename 'Dockerfile.arch'
//            //       additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
//            //       reuseNode true
//            //     }
//            //   }
//            //   steps {
//            //     dir("kevm-${env.VERSION}") {
//            //       unstash 'arch-kevm'
//            //       sh '''
//            //         sudo pacman -Syu --noconfirm
//            //         sudo pacman --noconfirm -U package/kevm-git-${VERSION}-1-x86_64.pkg.tar.xz
//            //         export PATH=$PATH:$(pwd)/.build/defn/vm
//            //         make test-interactive-firefly
//            //       '''
//            //     }
//            //   }
//            // }
//            stage('Upload Release') {
//              agent {
//                dockerfile {
//                  dir "kevm-${env.VERSION}/package"
//                  filename 'Dockerfile.arch'
//                  additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
//                  reuseNode true
//                }
//              }
//              steps {
//                dir("kevm-${env.VERSION}") {
//                  unstash 'src-kevm'
//                  dir("bionic") {
//                    unstash 'bionic-kevm'
//                  }
//                  dir("buster") {
//                    unstash 'buster-kevm'
//                  }
//                  dir("mojave") {
//                    unstash 'mojave-kevm'
//                  }
//                  // dir("arch") {
//                  //   unstash 'arch-kevm'
//                  // }
//                  sh '''
//                    release_tag="v${VERSION}-$(git rev-parse --short HEAD)"
//                    make release.md KEVM_RELEASE_TAG=${release_tag}
//                    mv bionic/kevm_${VERSION}_amd64.deb bionic/kevm_${VERSION}_amd64_bionic.deb
//                    mv buster/kevm_${VERSION}_amd64.deb buster/kevm_${VERSION}_amd64_buster.deb
//                    LOCAL_BOTTLE_NAME=$(echo mojave/kevm--${VERSION}.mojave.bottle*.tar.gz)
//                    BOTTLE_NAME=$(echo $LOCAL_BOTTLE_NAME | sed 's!kevm--!kevm-!')
//                    mv $LOCAL_BOTTLE_NAME $BOTTLE_NAME
//                    hub release create                                                                   \
//                        --attach kevm-${VERSION}-src.tar.gz"#Source tar.gz"                              \
//                        --attach bionic/kevm_${VERSION}_amd64_bionic.deb"#Ubuntu Bionic (18.04) Package" \
//                        --attach buster/kevm_${VERSION}_amd64_buster.deb"#Debian Buster (10) Package"    \
//                        --attach $BOTTLE_NAME"#Mac OS X Homebrew Bottle"                                 \
//                        --file "release.md" "${release_tag}"
//                   #      --attach arch/kevm-git-${VERSION}-1-x86_64.pkg.tar.xz"#Arch Package"             \
//                  '''
//                }
//              }
//            }
//            stage('Update Firefly Dependencies') {
//              steps {
//                build job: 'rv-devops/master', propagate: false, wait: false                                     \
//                    , parameters: [ booleanParam(name: 'UPDATE_DEPS_SUBMODULE', value: true)                     \
//                                  , string(name: 'PR_REVIEWER', value: 'ehildenb')                               \
//                                  , string(name: 'UPDATE_DEPS_REPOSITORY', value: 'runtimeverification/firefly') \
//                                  , string(name: 'UPDATE_DEPS_SUBMODULE_DIR', value: 'deps/evm-semantics')       \
//                                  ]
//              }
//            }
//          }
//        }
//      }
//    }
  }
}
