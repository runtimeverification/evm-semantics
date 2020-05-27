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
  options { ansiColor('xterm') }
  stages {
    stage("Init title") {
      when { changeRequest() }
      steps { script { currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}" } }
    }
    stage('Build and Test') {
      when { changeRequest() }
      agent {
        dockerfile {
          additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
          args '-m 60g'
          label 'docker && !smol'
        }
      }
      stages {
        stage('K Dependencies') { steps { sh 'make deps  RELEASE=true'     } }
        stage('Build')          { steps { sh 'make build RELEASE=true -j6' } }
        stage('Test Execution') {
          failFast true
          options { timeout(time: 20, unit: 'MINUTES') }
          parallel {
            stage('Conformance (LLVM)') { steps { sh 'make test-conformance -j8 TEST_CONCRETE_BACKEND=llvm' } }
            stage('VM (Haskell)')       { steps { sh 'make test-vm -j8 TEST_CONCRETE_BACKEND=haskell'       } }
            stage('Conformance (Web3)') { steps { sh 'make test-web3 -j8'                                   } }
          }
        }
        stage('Proofs') {
          options {
            lock("proofs-${env.NODE_NAME}")
            timeout(time: 55, unit: 'MINUTES')
          }
          parallel {
            stage('Java + Haskell')    { steps { sh 'make test-prove -j6'                                                        } }
            stage('Haskell (dry-run)') { steps { sh 'make test-prove -j2 KPROVE_OPTIONS=--dry-run TEST_SYMBOLIC_BACKEND=haskell' } }
          }
        }
        stage('Test Interactive') {
          failFast true
          options { timeout(time: 35, unit: 'MINUTES') }
          parallel {
            stage('LLVM krun')      { steps { sh 'make test-interactive-run TEST_CONCRETE_BACKEND=llvm'           } }
            stage('Java krun')      { steps { sh 'make test-interactive-run TEST_CONCRETE_BACKEND=java'           } }
            stage('Haskell krun')   { steps { sh 'make test-interactive-run TEST_CONCRETE_BACKEND=haskell'        } }
            stage('LLVM Kast')      { steps { sh 'make test-parse TEST_CONCRETE_BACKEND=llvm'                     } }
            stage('Failing tests')  { steps { sh 'make test-failure TEST_CONCRETE_BACKEND=llvm'                   } }
            stage('Java KLab')      { steps { sh 'make test-klab-prove TEST_SYMBOLIC_BACKEND=java'                } }
            stage('Haskell Search') { steps { sh 'make test-interactive-search TEST_SYMBOLIC_BACKEND=haskell -j4' } }
            stage('KEVM help')      { steps { sh './kevm help'                                                    } }
          }
        }
      }
    }
    stage('Deploy') {
      when { branch 'master' }
      agent { dockerfile { reuseNode true } }
      stages {
        stage('Update Dependents') {
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
        stage('Jello Paper') {
          steps {
            sshagent(['2b3d8d6b-0855-4b59-864a-6b3ddf9c9d1a']) {
              dir("kevm-${env.VERSION}-jello-paper") {
                sh '''
                  git config --global user.email "admin@runtimeverification.com"
                  git config --global user.name  "RV Jenkins"
                  mkdir -p ~/.ssh
                  echo 'host github.com'                       > ~/.ssh/config
                  echo '    hostname github.com'              >> ~/.ssh/config
                  echo '    user git'                         >> ~/.ssh/config
                  echo '    identityagent SSH_AUTH_SOCK'      >> ~/.ssh/config
                  echo '    stricthostkeychecking accept-new' >> ~/.ssh/config
                  chmod go-rwx -R ~/.ssh
                  ssh github.com || true
                  git clone 'ssh://github.com/kframework/evm-semantics.git'
                  cd evm-semantics
                  git checkout -B gh-pages origin/master
                  rm -rf .build .gitignore .gitmodules cmake deps Dockerfile Jenkinsfile kast-json.py kevm kore-json.py LICENSE Makefile media package
                  git add ./
                  git commit -m 'gh-pages: remove unrelated content'
                  git fetch origin gh-pages
                  git merge --strategy ours FETCH_HEAD
                  git push origin gh-pages
                '''
              }
            }
          }
        }
      }
    }
  }
}
