# Maintainer: Everett Hildenbrandt <everett.hildenbrandt@runtimeverification.com>
pkgname=kevm
pkgver=r1834.6ced26e
pkgrel=1
epoch=
pkgdesc="K implementation of the Ethereum Virtual Machine (EVM)"
arch=('x86_64')
url="https://github.com/kframework/evm-semantics"
license=('custom')
groups=()
depends=('kframework')
makedepends=('pandoc' 'protobuf')
checkdepends=()
optdepends=()
provides=()
conflicts=()
replaces=()
backup=()
options=(!strip)
install=kevm.install
changelog=
source=('git+https://github.com/kframework/evm-semantics#tag=node-v0.0-alpha')
noextract=()
md5sums=('SKIP')
validpgpkeys=()

prepare() {
    mkdir -p "$pkgname-$pkgver"
    cd "$srcdir/evm-semantics"
    git submodule update --init --recursive
}

pkgver() {
    cd "$srcdir/evm-semantics"
    printf 'r%s.%s' "$(git rev-list --count HEAD)" "$(git rev-parse --short HEAD)"
}

build() {
    cd "$srcdir/evm-semantics"
    make build-node
}

package() {
	cd "$pkgname-$pkgver"
	make INSTALL_DIR="$pkgdir/" install
	install -Dm644 LICENSE "$pkgdir/usr/share/licenses/$pkgname/LICENSE"
}
